
module Example where

import Codec.Serialise (Serialise, serialise, deserialiseOrFail)

import Control.Arrow ((***))
import Control.Lens (makePrisms, (#))
import Control.Monad
import Control.Monad.Catch.Pure hiding (try)
import Control.Monad.Fail as Fail (MonadFail(fail))
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.Reader
import Control.Monad.State

import Data.Coerce
import Data.Default (def)
import Data.Foldable (for_)
import Data.Hashable (Hashable (hash))
import Data.Relation (Relates)
import Data.Traversable (for)
import Data.Union (Member (union))
import qualified Data.ByteString       as SBS
import qualified Data.ByteString.Char8 as SBSC
import qualified Data.ByteString.Lazy  as LBS
import qualified Data.Map as Map

import Data.Blockchain.Storage.AVL
  ( Proven, record, apply, rollback
  , insert, delete, lookup, require
  , autoCommit, record_
  , CacheT, Commit (..), try, genesis, pair
  )
import qualified Data.Tree.AVL as AVL

import qualified Database.Redis as DB

import GHC.Generics (Generic)

import System.Directory (removeDirectoryRecursive)

type Name = String

{-
  We will define the keys for our storage. I choose such names for constructors
  because we use `Member` interface, which will recognise concrete keys as part
  of the whole `Keys` type. All keys should be declared that way.

  Also, I recommend making the keys `data` types or `newtypes` - otherwise type
  inference might get a bit brittle.

  For this example, I will use `Data.Hashable` to provide hash algorithm -
  that's why there is a deriving of `Hashable`. For industrial use, you'd
  better equip some hash algo from `cryptonite` package. Hash collision attack
  are no joke.
-}

data Keys
  = K1 Balance
  | K2 Friends
  deriving stock    (Eq, Ord, Show, Generic)
  deriving anyclass (Hashable, Serialise)

newtype Balance = Balance { getBalance :: Name }
  deriving stock   (Eq, Ord, Show, Generic)
  deriving anyclass (Hashable, Serialise)

newtype Friends = Friends { getFriends :: Name }
  deriving stock    (Eq, Ord, Show, Generic)
  deriving anyclass (Hashable, Serialise)

makePrisms ''Keys

instance Member Balance Keys where union = _K1
instance Member Friends Keys where union = _K2

{-
  The same goes for values (except for comparison instances). Concrete value
  types can be just anything.
-}

data Values
  = V1  Word
  | V2 [Name]
  deriving stock    (Show, Generic)
  deriving anyclass (Hashable, Serialise)

makePrisms ''Values

instance Member  Word   Values where union = _V1
instance Member [Name]  Values where union = _V2

{-
  And the last bit - we help type inference by specifying which key type is
  bound to which value type. Under "help" I mean it won't work otherwise.
-}

instance Relates Balance  Word
instance Relates Friends [Name]

{-
  As I've said, we using the simplest hash available for our example.
-}

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

{-
  We plug that hash in. The best hash is one that has an instance for all
  standart types, or else you have to write 5 instances, for, let's say, quite
  mundane datatypes.
-}

instance Hashable a => AVL.ProvidesHash a Hash where
  getHash = Hash . hash

{-
  The datatypes are done, let's do it for action typess. There is no limitation
  of what transaction can be. You can even make a different types for different
  kinds of transactions.

  You can add gas costs or make it into some opcode VM, if you like.

  The block can be modelled as another type of transaction, where you apply "normal" transactions and check Proof-of-Work or Proof-of-Stake.

  The generation of Work/Stake proofs is out of scope for this library and this example. The "proof" in this text means "AVL+-proof", which is completely different thing.
-}

data Transaction
  = Pay       { tFrom :: Name, tTo :: Name, tAmount :: Word }
  | AddFriend { tAdd  :: Name, tTo :: Name }
   deriving stock (Eq, Show, Generic)

{-
  Another useful thing is exceptions, which could arise when you apply the
  transaction. We will define only one here (other being `NotFound`, which is
  already in the `avl-plus` package).
-}

data Overdraft = Overdraft
  { oWho        :: Name
  , oOnlyHas    :: Word
  , oTriedToPay :: Word
  }
  deriving (Show)

instance Exception Overdraft

{-
  Let's write an interpreter for our `Transaction` type. It has be a
  function that consumes a transaction and runs in a `CacheT` over any monad
  that can `Retrieve` parts of the tree from storage. The "any monad" part is
  crucial for allowing the _same_ interpreter to run on both light-clients and
  full-state clients.

  This way, you get `requre`, `lookup`, `insert` and `delete` operations which
  operate on the global map (the AVL+-tree). While in `CacheT`, you can't
  change the storage; to do so, you must feed the `CacheT` computation into
  either `autoCommit` or `manualCommit`. If you do so with `manualCommit`, to
  actually apply changes you need to call `commit` when you need it without any
  arguments inside `CacheT` context. The `manualCommit` is provided for the
  case you end with some pretty complex error recovery mechanism as a part of
  transaction application.

  I recommend sticking to `autoCommit`.

  Note: If you call `commit` in a block once, you cannot `autoCommit` this
  block, the compiler won't let you.

  In both cases, if an exception happens during evaluation, the state of the
  storage is restored to the one just before the call.

  Therefore, if at any point the evaluation cannot proceed, you pretty much
  just `throwM` an exception.
-}

interpret
  :: AVL.Retrieves Hash Keys Values m
  => Transaction
  -> CacheT c Hash Keys Values m ()
interpret tx = case tx of
  Pay from to (fromIntegral -> amount) -> do
    src  <- require (Balance from)
    dest <- require (Balance to)

    unless (src >= amount) $ do
      throwM Overdraft
        { oWho        = from
        , oOnlyHas    = src
        , oTriedToPay = amount
        }

    insert (Balance from) (src  - amount)
    insert (Balance to)   (dest + amount)

  AddFriend friend to -> do
    src <- require (Friends to)
    _   <- require (Friends friend)   -- check if the friend exists

    insert (Friends to) (friend : src)

{-
  And we're done with the business-logic part!

  Let's see what can we do with all the things we declared above. The first
  opetation is to `recordProof` of the transaction, so I can be run on any node,
  even the one without any storage.

  The proof is an excerpt from the storage with a size < `O(log2(N) * Changes)`,
  where `Changes` is a count of key-value pairs that were either written or
  read. If there is 1 G of key-value pairs and 20 were changed, the proof would contain below 20 * 30 tree nodes.

  Recording produces a `Proven` transaction along with evaluation result (if
  any). The `Proven` datatype is exported openly and is `Generic`, so you can
  derive some serialisation.
-}

recordTxs
  :: AVL.Appends Hash Keys Values m
  => [Transaction]
  -> CacheT 'Auto Hash Keys Values m [Proven Hash Keys Values Transaction]
recordTxs txs = do
  for txs \tx -> do
    record_ tx interpret

{-
  Second thing we can do is to apply the transaction. Note: we're not
  _commiting_ anything yet, the changes and new state are still in the cache.
-}

consumeTxs
  :: AVL.Appends Hash Keys Values m
  => [Proven Hash Keys Values Transaction]
  -> CacheT c Hash Keys Values m ()
consumeTxs txs = do
  for_ txs \tx -> do
    apply tx interpret

{-
  Third thing is to roll back; and yes, we do it with the same interpreter we
  _commit_ the transaction. The interpreter is needed because we need to be
  sure if the current state is reachable with the transaction from the point we
  rollback to.
-}

rollbackTxs
  :: AVL.Appends Hash Keys Values m
  => [Proven Hash Keys Values Transaction]
  -> CacheT c Hash Keys Values m ()
rollbackTxs txs = do
  for_ (reverse txs) \tx -> do
    rollback tx interpret

{-
  That's all we can do; lets define our nodes.

  The light-client (or just `Client`) goes first. It only stores the root hash
  of the AVL+-tree and can roll back via `Catch`. It can't read or write into
  storage, because there isn't any underneath it. So, we `throwM` on reads and
  ignore writes.
-}

type ClientNode = StateT Hash Catch

instance AVL.Retrieves Hash Keys Values ClientNode where
  retrieve = AVL.notFound

instance AVL.Appends Hash Keys Values ClientNode where
  getRoot = get
  setRoot = put
  massStore _kvs = do
    -- do nothing, we're client
    return ()

runOnClient :: Hash -> ClientNode a -> Either SomeException (a, Hash)
runOnClient initial action =
  runCatch do
    runStateT action initial

{-
  The full-state node (or `Server` node) definition is more mouthful.

  We will use Redis for simplicity, but any key-value storage can be used
  instead. You can even employ remote storage solution. After all, the inner
  scheme of storing prevents data corruption.
-}

newtype ServerNode a = ServerNode
  { runServerNode :: ReaderT SBS.ByteString DB.Redis a
  }
  deriving newtype
    ( Functor
    , Applicative
    , Monad
    , MonadIO
    , MonadThrow
    , MonadCatch
    )

{-
  Redis, why aren't you already?

  If I want some custom error handling, I'd wrap it in newtype anyway.
-}

instance MonadThrow DB.Redis where
  throwM e = DB.reRedis do
    throwM e

instance MonadCatch DB.Redis where
  catch ma handler = DB.reRedis do
    DB.unRedis ma `catch` (DB.unRedis . handler)

instance MonadFail DB.Redis where
  fail = DB.reRedis . Fail.fail

{-
  I will omit the source of these two methods. They are short though and they
  do exactly what you'd expect them to do.

  They are ugly because `Codec.Serialise` and `Redis` use different types of `Bytestrings`.
-}

encode :: Serialise a => a -> SBS.ByteString
encode = LBS.toStrict . serialise

decode :: Serialise a => SBS.ByteString -> Maybe a
decode = either (const Nothing) Just . deserialiseOrFail . LBS.fromStrict

readKVS
  :: (Serialise k, Serialise v, Show k)
  => k
  -> ServerNode (Maybe v)
readKVS h = do
  prefix <- ServerNode ask
  eVal   <- ServerNode $ lift do
    DB.get (prefix <> encode h)

  case eVal of
    Right it -> do
      return (it >>= decode)

    _ ->
      AVL.notFound h

writeKVS
  :: (Serialise k, Serialise v)
  => [(k, v)]
  -> ServerNode ()
writeKVS kvs = do
  prefix <- ServerNode ask
  _ <- ServerNode $ lift do
    DB.mset (map (((prefix <>) . encode) *** encode) kvs)

  return ()

{-
  The next thing is to connect AVL+ to the Redis.
-}

instance AVL.Retrieves Hash Keys Values ServerNode where
  retrieve h = do
    node <- readKVS h
    maybe (AVL.notFound h) return node

{-
  It is crucial to throw `AVL.NoRootExists` here, not `AVL.NotFound`.

  TODO: make this method return `Maybe hash` instead.
-}

instance AVL.Appends Hash Keys Values ServerNode where
  getRoot = do
    mroot <- readKVS "root"
    maybe (throwM AVL.NoRootExists) return mroot

  setRoot h = do
    writeKVS [("root", h)]

  massStore = writeKVS

runOnRedisShard :: String -> ServerNode a -> DB.Redis a
runOnRedisShard dbName action = do
  runServerNode action `runReaderT` coerce (SBSC.pack dbName)

{-
  These two methods are used as a part of example test application to visualise
  the process.
-}

printState
  :: AVL.Appends Hash Keys Values m
  => MonadIO m
  => String
  -> m ()
printState msg = do
  root <- AVL.currentRoot

  liftIO do
    putStrLn ("  " ++ msg ++ ":")
    putStrLn ("    root hash: " ++ show (AVL.rootHash root))
    putStrLn  "    keys/values: "

  list <- AVL.toList root

  liftIO do
    for_ list \(k, v) ->
      putStrLn ("      " ++ show k ++ ": " ++ show v)

tryCase
  :: AVL.Appends Hash Keys Values m
  => MonadIO m
  => Show a
  => String
  -> CacheT 'Auto Hash Keys Values m a
  -> m (Maybe a)
tryCase msg action = do
  liftIO do
    putStrLn  ""
    putStrLn   msg
    putStrLn  "=="

  printState "before"

  res <- try $ autoCommit action

  printState "after"

  liftIO do
    putStrLn  "  result:"
    putStrLn ("    " ++ show res)

  return (either (const Nothing) Just res)

newtype Omitted a = Omitted a

instance Show (Omitted a) where
  show _ = "<omitted>"

{-
  Warning, this method wipes out the Redis database!

  We will test on two nodes, both of which are full-state Redis-based ones.

  Let's see, how does it work together:
-}
test = do
  DB.flushdb

  {-
    First, we need to initialise both nodes with identical data.
  -}
  let
    initialData =
      [ pair (Balance "Petua",   200)
      , pair (Friends "Petua",   [])

      , pair (Balance "Vasua",   300)
      , pair (Friends "Vasua",   [])

      , pair (Balance "Maloney", 10)
      , pair (Friends "Maloney", [])
      ]

  runOnRedisShard "test" do
    genesis initialData

  runOnRedisShard "test2" do
    genesis initialData

  {-
    We can start recording transactions now (transaction recorded is being
    applied at the same time).

    Note: no morally ambiguos thing is happening in the transaction.
  -}
  Just ptxs <- runOnRedisShard "test" do
    tryCase "Making good txs" do
      recordTxs
        [ Pay       { tFrom = "Vasua", tTo = "Petua", tAmount = 200 }
        , AddFriend { tAdd  = "Vasua", tTo = "Petua" }
        ]

  {-
    TODO: find why the following block fails.
  -}
  runOnRedisShard "test2" do
    tryCase "Applying good txs" do
      consumeTxs ptxs

  ptxs' <- runOnRedisShard "test" $ do
    autoCommit do
      recordTxs
        [ Pay       { tFrom = "Vasua",   tTo = "Petua", tAmount = 100 }
        , AddFriend { tAdd  = "Maloney", tTo = "Petua" }
        ]

  runOnRedisShard "test2" do
    tryCase "Applying other txs" do
      consumeTxs ptxs'

  runOnRedisShard "test" do
    tryCase "Rolling back wrong txs" do
      rollbackTxs ptxs

  Nothing <- runOnRedisShard "test" do
    tryCase "Making bad txs#1" do
      recordTxs
        [ Pay       { tFrom = "Maloney", tTo = "Petua", tAmount = 200 }
        , AddFriend { tAdd  = "Vasua",   tTo = "Petua" }
        ]

    tryCase "Making bad txs#2" do
      recordTxs
        [ Pay       { tFrom = "Maloney", tTo = "Petua", tAmount = 10 }
        , AddFriend { tAdd  = "Haxxor",  tTo = "Petua" }
        ]

  runOnRedisShard "test" do
    tryCase "Rolling back good txs" do
      rollbackTxs ptxs'

  runOnRedisShard "test" do
    tryCase "Rolling back now good txs" do
      rollbackTxs ptxs

  return ()

main = do
  conn <- DB.checkedConnect DB.defaultConnectInfo
  DB.runRedis conn test
