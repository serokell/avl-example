
module Example where

import Codec.Serialise (Serialise, serialise, deserialiseOrFail)

import Control.Arrow ((***))
import Control.Lens (makePrisms, (#))
import Control.Monad (unless, join)
import Control.Monad.Reader
  ( ReaderT (runReaderT)
  , ask
  , asks
  )
import Control.Monad.State
  ( StateT (runStateT)
  , execStateT
  , get
  , put
  , gets
  , modify
  )
import Control.Monad.Catch.Pure
  ( Exception
  , SomeException
  , Catch
  , runCatch
  , throwM
  , bracket
  , catchIOError
  )
import Control.Monad.IO.Class (MonadIO (liftIO))

import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString      as SBS
import Data.Default (def)
import Data.Foldable (for_)
import Data.Traversable (for)
import Data.Hashable (Hashable (hash))
import qualified Data.Map as Map
import Data.Union (Member (union))
import Data.Relation (Relates)
import Data.Tree.AVL.Adapter
  ( Proven, record, apply, rollback
  , insert, delete, lookup, require
  , transact, transactAndRethrow, record_
  , SandboxT
  )
import qualified Data.Tree.AVL as AVL

import qualified Database.RocksDB as Rocks

import GHC.Generics (Generic)

import System.Directory (removeDirectoryRecursive)

type Name = String

data Keys
  = K1 Balance
  | K2 Friends
  deriving stock    (Eq, Ord, Show, Generic)
  deriving anyclass (Hashable, Serialise)

newtype Balance = Balance { getBalance :: Name }
  deriving stock   (Eq, Ord, Show, Generic)
  deriving newtype (Hashable)
  deriving anyclass (Serialise)

newtype Friends = Friends { getFriends :: Name }
  deriving stock    (Eq, Ord, Show, Generic)
  deriving newtype  (Hashable)
  deriving anyclass (Serialise)

data Values
  = V1 Word
  | V2 [Name]
  deriving stock    (Eq, Ord, Show, Generic)
  deriving anyclass (Hashable, Serialise)

newtype Hash = Hash { getHash :: Int }
  deriving stock   (Eq, Ord, Generic)
  deriving newtype (Hashable, Serialise)

instance Show Hash where
  show
    = reverse
    . map     ("0123456789abcdef" !!)
    . take      16
    . map     (`mod` 16)
    . iterate (`div` 16)
    . getHash

makePrisms ''Values
makePrisms ''Keys

instance Member Balance Keys   where union = _K1
instance Member Friends Keys   where union = _K2

instance Member Word   Values where union = _V1
instance Member [Name] Values where union = _V2

instance Relates Balance Word
instance Relates Friends [Name]

instance Hashable a => AVL.ProvidesHash a Hash where
  getHash = Hash . hash

data Transaction
  = Pay       { tFrom :: Name, tTo :: Name, tAmount :: Word }
  | AddFriend { tAdd  :: Name, tTo :: Name }
   deriving stock (Eq, Show, Generic)

data Overdraft = Overdraft
  { oWho        :: Name
  , oOnlyHas    :: Word
  , oTriedToPay :: Word
  }
  deriving (Show)

instance Exception Overdraft

interpret
  :: AVL.Retrieves Hash Keys Values m
  => Transaction -> SandboxT Hash Keys Values m ()
interpret tx = case tx of
  Pay from to (fromIntegral -> amount) -> do
    src  <- require (Balance from)
    dest <- require (Balance to)

    unless (src >= amount) $ do
      throwM $ Overdraft
        { oWho        = from
        , oOnlyHas    = src
        , oTriedToPay = amount
        }

    insert (Balance from) (src - amount)
    insert (Balance to)   (dest + amount)

  AddFriend friend to -> do
    src <- require (Friends to)
    _   <- require (Friends friend)   -- check if the friend exists

    insert (Friends to) (friend : src)

consumeTxs
  :: AVL.Appends Hash Keys Values m
  => [Proven Hash Keys Values Transaction]
  -> m ()
consumeTxs txs = do
  transactAndRethrow @SomeException $ do
    for_ txs $ \tx -> do
      apply tx interpret

rollbackTxs
  :: AVL.Appends Hash Keys Values m
  => [Proven Hash Keys Values Transaction]
  -> m ()
rollbackTxs txs = do
  transactAndRethrow @SomeException $ do
    for_ (reverse txs) $ \tx -> do
      rollback tx interpret

type ClientNode = StateT Hash Catch

instance AVL.KVRetrieve Hash Keys Values ClientNode where
  retrieve = AVL.notFound

instance AVL.KVAppend Hash Keys Values ClientNode where
  getRoot = get
  setRoot = put
  massStore _kvs = do
    -- do nothing, we're client
    return ()

runOnClient :: Hash -> ClientNode a -> Either SomeException (a, Hash)
runOnClient initial action =
  runCatch $ runStateT action initial

type ServerState = (Map.Map Hash (AVL.Rep Hash Keys Values), Maybe Hash)
type ServerNode  = ReaderT (Rocks.DB, Rocks.ReadOptions, Rocks.WriteOptions) IO

encode :: Serialise a => a -> SBS.ByteString
encode = LBS.toStrict . serialise

decode :: Serialise a => SBS.ByteString -> Maybe a
decode = either (const Nothing) Just . deserialiseOrFail . LBS.fromStrict

readRocks
  :: (Serialise k, Serialise v)
  => k
  -> ServerNode (Maybe v)
readRocks h = do
  (db, ro, _) <- ask
  res <- liftIO $ (decode <$>) <$> Rocks.get db ro (encode h)
  return $ join res

writeRocks
  :: (Serialise k, Serialise v)
  => [(k, v)]
  -> ServerNode ()
writeRocks kvs = do
  (db, _, rw) <- ask
  liftIO $ Rocks.write db rw (map (uncurry Rocks.Put . (encode *** encode)) kvs)

instance AVL.KVRetrieve Hash Keys Values ServerNode where
  retrieve h = do
    node <- readRocks h
    maybe (AVL.notFound h) return node

instance AVL.KVAppend Hash Keys Values ServerNode where
  getRoot = do
    mroot <- readRocks "root"
    maybe (throwM AVL.NoRootExists) return mroot

  setRoot h = do
    writeRocks [("root", h)]

  massStore = writeRocks

genesis :: [(Keys, Values)] -> ServerNode ()
genesis kvs = do
  AVL.initialiseStorageIfNotAlready kvs

pair
  :: ( Member k keys
     , Member v values
     , Relates k v
     )
  => (k, v)
  -> (keys, values)
pair (k, v) = (union # k, union # v)

runOnRocksDB :: FilePath -> ServerNode a -> IO a
runOnRocksDB dbName action = do
  let
    opts = def
      { Rocks.createIfMissing = True
      }

  bracket (Rocks.open dbName opts) Rocks.close $ \db -> do
    runReaderT action (db, def, def)

recordTxs
  :: AVL.Appends Hash Keys Values m
  => [Transaction]
  -> m [Proven Hash Keys Values Transaction]
recordTxs txs = do
  for txs $ \tx -> do
    record_ tx interpret

printState
  :: AVL.Appends Hash Keys Values m
  => MonadIO m
  => String
  -> m ()
printState msg = do
  root <- AVL.currentRoot

  liftIO $ putStrLn ("  " ++ msg ++ ":")
  liftIO $ putStrLn ("    root hash: " ++ show (AVL.rootHash root))
  liftIO $ putStrLn  "    keys/values: "

  list <- AVL.toList root

  for_ list $ \(k, v) ->
    liftIO $ putStrLn $ "      " ++ show k ++ ": " ++ show v

tryCase
  :: AVL.Appends Hash Keys Values m
  => MonadIO m
  => Show a
  => String
  -> m a
  -> m (Maybe a)
tryCase msg action = do
  liftIO $ putStrLn  ""
  liftIO $ putStrLn   msg
  liftIO $ putStrLn  "=="

  printState "before"

  res <- transact @SomeException action

  printState "after"

  liftIO $ putStrLn  "  result:"
  liftIO $ putStrLn ("    " ++ show res)

  return (either (const Nothing) Just res)

newtype Omitted a = Omitted a

instance Show (Omitted a) where
  show _ = "<omitted>"

tryGoodTransactions = do
  removeDirectoryRecursive "test"  `catchIOError` \e -> print e
  removeDirectoryRecursive "test2" `catchIOError` \e -> print e

  let
    seedWithData =
      genesis
        [ pair (Balance "Petua",   200)
        , pair (Friends "Petua",   [])

        , pair (Balance "Vasua",   300)
        , pair (Friends "Vasua",   [])

        , pair (Balance "Maloney", 10)
        , pair (Friends "Maloney", [])
        ]


  runOnRocksDB "test" seedWithData
  runOnRocksDB "test2" seedWithData

  Just (Omitted ptxs) <- runOnRocksDB "test" $ do
    ptxs <- tryCase "Making good txs" $ Omitted <$> recordTxs
      [ Pay       { tFrom = "Vasua", tTo = "Petua", tAmount = 200 }
      , AddFriend { tAdd  = "Vasua", tTo = "Petua" }
      ]
    return ptxs

  ptxs' <- runOnRocksDB "test" $ do
    ptxs <- transactAndRethrow @SomeException $ recordTxs
      [ Pay       { tFrom = "Vasua",   tTo = "Petua", tAmount = 100 }
      , AddFriend { tAdd  = "Maloney", tTo = "Petua" }
      ]
    return ptxs

  Nothing <- runOnRocksDB "test" $ do
    tryCase "Making bad txs#1" $ recordTxs
      [ Pay       { tFrom = "Maloney", tTo = "Petua", tAmount = 200 }
      , AddFriend { tAdd  = "Vasua",   tTo = "Petua" }
      ]

    tryCase "Making bad txs#2" $ recordTxs
      [ Pay       { tFrom = "Maloney", tTo = "Petua", tAmount = 10 }
      , AddFriend { tAdd  = "Haxxor",  tTo = "Petua" }
      ]

  runOnRocksDB "test2" $ do
    tryCase "Applying good txs" $ consumeTxs ptxs

  runOnRocksDB "test2" $ do
    tryCase "Applying other txs" $ consumeTxs ptxs'

  runOnRocksDB "test" $ do
    tryCase "Rolling back wrong txs" $ rollbackTxs ptxs

  runOnRocksDB "test" $ do
    tryCase "Rolling back good txs" $ rollbackTxs ptxs'

  runOnRocksDB "test" $ do
    tryCase "Rolling back now good txs" $ rollbackTxs ptxs

  return ()

main = tryGoodTransactions
