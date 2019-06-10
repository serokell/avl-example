
import Data.Tree.AVL.Adapter

import Control.Monad.State
import Control.Monad.Catch
import Control.Monad.Catch.Pure
import Data.Foldable (for_)
import Data.Traversable (for)
import Data.Hashable
import qualified Data.Map as Map
import Data.Tree.AVL.Adapter
  ( Proven, record, apply, rollback
  , insert, delete, lookup, require
  , transact, transactAndRethrow
  , SandboxT
  )
import qualified Data.Tree.AVL as AVL
import GHC.Generics (Generic)

import qualified Debug.Trace as Debug

type Key = String  -- a name

data Value = Account
  { vBalance :: Word
  , vFriends :: [String]
  }
  deriving (Eq, Show, Generic)

newtype Hash = Hash { getHash :: Int }
  deriving (Eq, Ord, Generic)

instance Show Hash where
  show
    = reverse
    . map     ("0123456789abcdef" !!)
    . take      16
    . map     (`mod` 16)
    . iterate (`div` 16)
    . getHash

instance Hashable Value
instance Hashable Hash

instance Hashable a => AVL.ProvidesHash a Hash where
  getHash = Hash . hash

data Transaction
  = Pay       { tFrom :: String, tTo :: String, tAmount :: Word }
  | AddFriend { tAdd  :: String, tTo :: String }
   deriving (Eq, Show, Generic)

data Overdraft = Overdraft
  { oWho        :: Key
  , oOnlyHas    :: Word
  , oTriedToPay :: Word
  }
  deriving (Show)

instance Exception Overdraft

interpret
  :: AVL.Retrieves Hash Key Value m
  => Transaction -> SandboxT Hash Key Value m ()
interpret tx = case tx of
  Pay from to (fromIntegral -> amount) -> do
    src  <- require from
    dest <- require to

    unless (vBalance src >= amount) $ do
      throwM $ Overdraft
        { oWho        = from
        , oOnlyHas    = vBalance src
        , oTriedToPay = amount
        }

    insert from src  { vBalance = vBalance src - amount }
    insert to   dest { vBalance = vBalance dest + amount }

  AddFriend friend to -> do
    src <- require to
    _   <- require friend   -- check if the friend exists

    insert to src { vFriends = friend : vFriends src }

consumeTxs
  :: AVL.Appends Hash Key Value m
  => [Proven Hash Key Value Transaction]
  -> m ()
consumeTxs txs = do
  transactAndRethrow @SomeException $ do
    for_ txs $ \tx -> do
      apply tx interpret

rollbackTxs
  :: AVL.Appends Hash Key Value m
  => [Proven Hash Key Value Transaction]
  -> m ()
rollbackTxs txs = do
  transactAndRethrow @SomeException $ do
    for_ (reverse txs) $ \tx -> do
      rollback tx interpret

type ClientNode = StateT Hash Catch

instance AVL.KVAppend Hash Key Value ClientNode where
  getRoot = get
  setRoot = put

instance AVL.KVStore Hash Key Value ClientNode where
  massStore _kvs = do
    -- do nothing, we're client
    return ()

instance AVL.KVRetrieve Hash Key Value ClientNode where
  retrieve h = throwM $ AVL.NotFound h

runOnClient :: Hash -> ClientNode a -> Either SomeException (a, Hash)
runOnClient initial action =
  runCatch $ runStateT action initial

type ServerState = (Map.Map Hash (AVL.Isolated Hash Key Value), Maybe Hash)
type ServerNode  = StateT ServerState IO

instance AVL.KVAppend Hash Key Value ServerNode where
  getRoot   = gets snd >>= maybe (throwM AVL.NoRootExists) return
  setRoot h = modify $ \(store, _) -> (store, Just h)

instance AVL.KVStore Hash Key Value ServerNode where
  massStore kvs = do
    modify $ \(store, h) -> (Map.fromList kvs <> store, h)

instance AVL.KVRetrieve Hash Key Value ServerNode where
  retrieve h = do
    res <- gets (Map.lookup h . fst)
    maybe (throwM $ AVL.NotFound h) return res

genesis :: [(Key, Value)] -> IO ServerState
genesis kvs = do
  flip execStateT (Map.empty, Nothing) $ do
    AVL.initialiseStorageIfNotAlready kvs
    h <- AVL.getRoot
    s <- get
    return (s, h)

runOnServer :: ServerState -> ServerNode a -> IO (a, ServerState)
runOnServer initial action =
  runStateT action initial

makeGoodTxs
  :: AVL.Appends Hash Key Value m
  => [Transaction]
  -> m [Proven Hash Key Value Transaction]
makeGoodTxs txs = do
  for txs $ \tx -> do
    record_ tx interpret

printState
  :: AVL.Appends Hash Key Value m
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
    liftIO $ putStrLn $ "      " ++ k ++ ": " ++ show v

tryCase
  :: AVL.Appends Hash Key Value m
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
  gen@ (_, Just h) <- genesis
    [ ("Petua",   Account 200 [])
    , ("Vasua",   Account 300 [])
    , ("Maloney", Account 10  [])
    ]

  (Just (Omitted ptxs), gen1) <- runOnServer gen $ do
    ptxs <- tryCase "Making good txs" $ Omitted <$> makeGoodTxs
      [ Pay       { tFrom = "Vasua", tTo = "Petua", tAmount = 200 }
      , AddFriend { tAdd  = "Vasua", tTo = "Petua" }
      ]
    return ptxs

  (ptxs', _) <- runOnServer gen1 $ do
    ptxs <- transactAndRethrow @SomeException $ makeGoodTxs
      [ Pay       { tFrom = "Vasua",   tTo = "Petua", tAmount = 100 }
      , AddFriend { tAdd  = "Maloney", tTo = "Petua" }
      ]
    return ptxs

  (Nothing, _) <- runOnServer gen $ do
    tryCase "Making bad txs#1" $ makeGoodTxs
      [ Pay       { tFrom = "Maloney", tTo = "Petua", tAmount = 200 }
      , AddFriend { tAdd  = "Vasua",   tTo = "Petua" }
      ]

    tryCase "Making bad txs#2" $ makeGoodTxs
      [ Pay       { tFrom = "Maloney", tTo = "Petua", tAmount = 10 }
      , AddFriend { tAdd  = "Haxxor",  tTo = "Petua" }
      ]

  (_, gen1) <- runOnServer gen $ do
    tryCase "Applying good txs" $ consumeTxs ptxs

  (_, gen2) <- runOnServer gen $ do
    tryCase "Applying other txs" $ consumeTxs ptxs'

  (_, _) <- runOnServer gen1 $ do
    tryCase "Rolling back good txs" $ rollbackTxs ptxs

  (_, _) <- runOnServer gen1 $ do
    tryCase "Rolling back other txs" $ rollbackTxs ptxs'

  return ()

main = tryGoodTransactions
