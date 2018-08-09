{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies, TypeFamilies,
             FlexibleContexts, ScopedTypeVariables, GADTs, RankNTypes,
             GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
module ConsumerProtocol where

import Data.Word
import Data.Functor (($>))
import Data.Functor.Const (Const)
import Data.Functor.Sum (Sum (..))
import Data.List (tails, foldl')
--import Data.Maybe
import Data.Hashable
--import qualified Data.Set as Set
import qualified Data.Map as Map
import           Data.Map (Map)
import           Data.PriorityQueue.FingerTree (PQueue)
import qualified Data.PriorityQueue.FingerTree as PQueue
import Data.Time (NominalDiffTime)
import Data.Time.Clock.POSIX (getPOSIXTime)
import Data.Time.Units (Microsecond, toMicroseconds)
import Data.Void (Void)

import Control.Applicative
import Control.Monad
import Control.Monad.Free (Free (..))
import Control.Monad.Free as Free
import Control.Concurrent (forkIO, threadDelay)
import Control.Concurrent.STM (STM, retry)
import qualified Control.Concurrent.MVar as MVar
import Control.Exception (assert)
import Control.Monad.ST.Lazy
import Data.IORef (IORef, modifyIORef')
import Data.STRef.Lazy
import System.Random (StdGen, mkStdGen, randomR)

import Test.QuickCheck

import ChainExperiment2


--
-- IPC based protocol
--


class Monad m => MonadSay m where
  say :: String -> m ()

instance MonadSay IO where
  -- TODO: upgrade MonadSay to logging
  say    msg = putStrLn msg

class Monad m => MonadProbe m where
  type Probe m :: * -> *
  probeOutput :: Probe m a -> a -> m ()

newtype IOProbe s a = IOProbe (IORef [(NominalDiffTime, a)])

instance MonadProbe IO where
  type Probe IO = IOProbe Void
  probeOutput (IOProbe p) o = do
    time <- getPOSIXTime
    modifyIORef' p ((time, o):)

class TimeMeasure (Time m) => MonadTimer m where
  type Time m :: *
  timer :: Duration (Time m) -> m () -> m ()

instance MonadTimer IO where
  type Time IO = Microsecond
  timer t io = void $ forkIO $ do
    threadDelay $ fromIntegral $ toMicroseconds t
    io

class (Ord t, Ord (Duration t), Num (Duration t)) => TimeMeasure t where
  type Duration t :: *

  diffTime :: t -> t -> Duration t
  addTime  :: Duration t -> t -> t

instance TimeMeasure Microsecond where
  type Duration Microsecond = Microsecond
  diffTime = (-)
  addTime  = (+)

class Monad m => MonadConc m where
  type MVar m :: * -> *

  fork         :: m () -> m ()
  newEmptyMVar :: m (MVar m a)
  newMVar      :: a -> m (MVar m a)
  takeMVar     :: MVar m a -> m a
  tryTakeMVar  :: MVar m a -> m (Maybe a)
  putMVar      :: MVar m a -> a -> m ()
  tryPutMVar   :: MVar m a -> a -> m Bool

  readMVar     :: MVar m a -> m a
  readMVar v = do x <- takeMVar v; putMVar v x; return x

newtype IOMVar s a = IOMVar { runIOMVar :: MVar.MVar a }

instance MonadConc IO where
  type MVar IO = MVar.MVar

  fork io      = void $ forkIO io
  newEmptyMVar = MVar.newEmptyMVar
  newMVar      = MVar.newMVar
  takeMVar     = MVar.takeMVar
  tryTakeMVar  = MVar.tryTakeMVar
  putMVar      = MVar.putMVar
  tryPutMVar   = MVar.tryPutMVar

class Monad m => MonadSendRecv m where
  type BiChan m :: * -> * -> *

  newChan :: m (BiChan m s r)
  sendMsg :: BiChan m s r -> s -> m ()
  recvMsg :: BiChan m s r -> m r

data SendRecvF (chan :: * -> * -> *) a where
  NewChanF :: (chan s r -> a) -> SendRecvF chan a
  SendMsgF :: chan s r -> s -> a -> SendRecvF chan a
  RecvMsgF :: chan s r -> (r -> a) -> SendRecvF chan a

instance Functor (SendRecvF chan) where
  fmap f (NewChanF k)     = NewChanF (f . k)
  fmap f (SendMsgF c s a) = SendMsgF c s (f a)
  fmap f (RecvMsgF c k)   = RecvMsgF c (f . k)

instance MonadSendRecv (Free (SendRecvF chan)) where
  type BiChan (Free (SendRecvF chan)) = chan
  newChan        = Free.liftF $ NewChanF id
  sendMsg chan s = Free.liftF $ SendMsgF chan s ()
  recvMsg chan   = Free.liftF $ RecvMsgF chan id

instance Functor f => MonadSendRecv (Free (Sum f (SendRecvF chan))) where
  type BiChan (Free (Sum f (SendRecvF chan)))= chan
  newChan        = Free.liftF $ InR (NewChanF id)
  sendMsg chan s = Free.liftF $ InR (SendMsgF chan s ())
  recvMsg chan   = Free.liftF $ InR (RecvMsgF chan id)

-- | In this protocol the consumer always initiates things and the producer
-- replies. This is the type of messages that the consumer sends.
data MsgConsumer = MsgRequestNext
--                 | MsgInformChain

data MsgProducer = MsgRollForward  Block
                 | MsgRollBackward Point
                 | MsgAwaitReply

{-
data ProtcolM s r a where
  ReturnP :: a -> ProtcolM s r a
  FailP   :: String -> ProtcolM s r a
  SendMsg :: s -> ProtcolM s r ()
  RecvMsg :: ProtcolM s r r
-}

consumerSideProtocol1 :: forall m.
                         (MonadSendRecv m, MonadSay m)
                      => (Block -> m ())
                      -> (Point -> m ())
                      -> BiChan m MsgConsumer MsgProducer
                      -> m ()
consumerSideProtocol1 addBlock rollbackTo chan =
    --TODO: do the protocol initiation phase
    requestNext
  where
    requestNext :: m ()
    requestNext = do
      sendMsg chan MsgRequestNext
      reply <- recvMsg chan
      handleChainUpdate reply
      requestNext

    handleChainUpdate :: MsgProducer -> m ()
    handleChainUpdate MsgAwaitReply = do
      say ("awaiting real reply")

    handleChainUpdate (MsgRollForward  b) = do
      addBlock b
      say ("ap blocks from point X to point Y")
      return ()

    handleChainUpdate (MsgRollBackward p) = do
      say ("rolling back N blocks from point X to point Y")
      return ()

producerSideProtocol1 :: forall m.
                         (MonadSendRecv m, MonadSay m)
                      => (ReaderId -> m (Maybe (ConsumeChain Block)))
                      -> (ReaderId -> m (ConsumeChain Block))
                      -> ReaderId
                      -> BiChan m MsgProducer MsgConsumer
                      -> m ()
producerSideProtocol1 tryReadChainUpdate readChainUpdate rid chan =
    --TODO: do the protocol initiation phase
    awaitRequest
  where
    awaitRequest = do
      msg <- recvMsg chan
      case msg of
        MsgRequestNext -> handleNext

    handleNext = do
      mupdate <- tryReadChainUpdate rid
      case mupdate of
        -- Reader is at the head, have to wait for producer state changes.
        Nothing -> do
          sendMsg chan MsgAwaitReply
          update <- readChainUpdate rid
          handleChainUpdate update

        Just update ->
          handleChainUpdate update

    handleChainUpdate update = do
      sendReply update
      awaitRequest

    sendReply :: ConsumeChain Block -> m ()
    sendReply (RollForward  b) = sendMsg chan (MsgRollForward b)
    sendReply (RollBackward p) = sendMsg chan (MsgRollBackward p)

--
-- Simulation of composition of producer and consumer
--


-- | Given two sides of a protocol, ...
--
simulateWire
  :: forall probe time mvar g p c s .
     (SimChan mvar p c -> Free (Sum (SimF (SendRecvF (SimChan mvar)) probe time mvar s) (SendRecvF (SimChan mvar))) ())
  -> (SimChan mvar c p -> Free (Sum (SimF (SendRecvF (SimChan mvar)) probe time mvar s) (SendRecvF (SimChan mvar))) ())
  -> Free (Sum (SimF (SendRecvF (SimChan mvar)) probe time mvar s) (SendRecvF (SimChan mvar))) ()
simulateWire protocolSideA protocolSideB = do
    chan <- newChan
    fork $ protocolSideA chan
    fork $ protocolSideB (flipSimChan chan)
    return ()

-- |
-- Simulation monad for protocol testing.
--
-- The first argument @g@ allows to extend @SimF@ functor; for example by using
-- @'SendRecvF' chan@ functor inside @'Fork'@ or @'Timer'@.
--
-- A simpler approach would be just to include @'SendRecvF' chan@ constructors
-- in @'SimF'@, or hard code @'SendRecvF'@ in @'Fork'@ or @'Timer'@ directives.
data SimF (g :: * -> *) (probe :: * -> * -> *) time (mvar :: * -> *) s a where
  Fail         :: String -> SimF g probe time mvar s a

  Say          :: [String] -> b -> SimF g probe time mvar s b
  Probe        :: probe s o -> o -> b -> SimF g probe time mvar s b

  Timer        :: Duration time -> Free (Sum (SimF g probe time mvar s) g) () -> b -> SimF g probe time mvar s b

  Fork         :: Free (Sum (SimF g probe time mvar s) g) () -> b -> SimF g probe time mvar s b
  NewEmptyMVar :: (mvar a -> b) -> SimF g probe time mvar s b
  TakeMVar     :: mvar a -> (a -> b) -> SimF g probe time mvar s b
  PutMVar      :: mvar a ->  a -> b  -> SimF g probe time mvar s b
  TryTakeMVar  :: mvar a -> (Maybe a -> b) -> SimF g probe time mvar s b
  TryPutMVar   :: mvar a -> a -> (Bool -> b) -> SimF g probe time mvar s b

instance Functor (SimF g probe time mvar s) where
    fmap _ (Fail f)           = Fail f
    fmap f (Say ss b)         = Say ss $ f b
    fmap f (Probe p o b)      = Probe p o $ f b
    fmap f (Timer d s b)      = Timer d s $ f b
    fmap f (Fork s b)         = Fork s $ f b
    fmap f (NewEmptyMVar k)   = NewEmptyMVar (f . k)
    fmap f (TakeMVar v k)     = TakeMVar v (f . k)
    fmap f (PutMVar v a b)    = PutMVar v a $ f b
    fmap f (TryTakeMVar v k)  = TryTakeMVar v (f . k)
    fmap f (TryPutMVar v a k) = TryPutMVar v a (f . k)

type SimM (probe :: * -> * -> *) time (mvar :: * -> *) s a = Free (SimF (Const ()) probe time mvar s) a

data SimMVar g s a = SimMVar (STRef s (MVarContent g s a)) MVarTag
type MVarTag = Tag

newtype SimProbe s a = SimProbe (STRef s (ProbeTrace a))
type ProbeTrace a = [(VTime, a)]

newtype VTime         = VTime Int          deriving (Eq, Ord, Show)
newtype VTimeDuration = VTimeDuration Int  deriving (Eq, Ord, Show, Num, Enum, Real)

data MVarContent g s a
    = MVarEmpty  [a -> Thread g s] -- threads blocked in take
    | MVarFull a [(a, Thread g s)] -- threads blocked in put

type Action g s = Free (Sum (SimF g SimProbe VTime (SimMVar g s) s) g) ()
data Thread g s = Thread ThreadId (Action g s)
type ThreadId = ThreadTag
type ThreadTag = Tag
type Tag = String -- for annotating the trace

instance TimeMeasure VTime where
  type Duration VTime = VTimeDuration

  diffTime (VTime t) (VTime t') = VTimeDuration (t-t')
  addTime  (VTimeDuration d) (VTime t) = VTime (t+d)

instance MonadSay (Free (SimF g probe time mvar s)) where
  say msg = Free.liftF $ Say [msg] ()

instance Functor g => MonadSay (Free (Sum (SimF g probe time mvar s) g)) where
  say msg = Free.liftF $ InL $ Say [msg] ()

instance MonadProbe (Free (SimF g probe time mvar s)) where
  type Probe (Free (SimF g probe time mvar s)) = probe s
  probeOutput p o = Free.liftF $ Probe p o ()

instance Functor g => MonadProbe (Free (Sum (SimF g probe time mvar s) g)) where
  type Probe (Free (Sum (SimF g probe time mvar s) g)) = probe s
  probeOutput p o = Free.liftF $ InL $ Probe p o ()

instance (Functor g, TimeMeasure time) => MonadTimer (Free (SimF g probe time mvar s)) where
  type Time (Free (SimF g probe time mvar s)) = time
  timer t action = Free.liftF $ Timer t (Free.hoistFree InL action) ()

instance (Functor g, TimeMeasure time) => MonadTimer (Free (Sum (SimF g probe time mvar s) g)) where
  type Time (Free (Sum (SimF g probe time mvar s) g)) = time
  timer t action = Free.liftF $ InL $ Timer t action ()

instance Functor g => MonadConc (Free (SimF g probe time mvar s)) where
  type MVar (Free (SimF g probe time mvar s)) = mvar

  fork          task = Free.liftF $ Fork (Free.hoistFree (InL @_ @g) task) ()
  newEmptyMVar       = Free.liftF $ NewEmptyMVar id
  newMVar          x = do mvar <- newEmptyMVar; putMVar mvar x; return mvar
  tryPutMVar  mvar x = Free.liftF $ TryPutMVar mvar x id
  tryTakeMVar mvar   = Free.liftF $ TryTakeMVar mvar id
  takeMVar    mvar   = Free.liftF $ TakeMVar mvar id
  putMVar     mvar x = Free.liftF $ PutMVar  mvar x ()

instance Functor g => MonadConc (Free (Sum (SimF g probe time mvar s) g)) where
  type MVar (Free (Sum (SimF g probe time mvar s) g)) = mvar

  fork task          = Free $ InL $ Fork task (return ())
  newEmptyMVar       = Free.liftF $ InL $ NewEmptyMVar id
  newMVar          x = do mvar <- newEmptyMVar; putMVar mvar x; return mvar
  tryPutMVar  mvar x = Free.liftF $ InL $ TryPutMVar mvar x id
  tryTakeMVar mvar   = Free.liftF $ InL $ TryTakeMVar mvar id
  takeMVar    mvar   = Free.liftF $ InL $ TakeMVar mvar id
  putMVar     mvar x = Free.liftF $ InL $ PutMVar  mvar x ()

instance Functor g => MonadSendRecv (Free (SimF g probe time mvar s)) where
  type BiChan (Free (SimF g probe time mvar s)) = SimChan mvar

  newChan = SimChan <$> newEmptyMVar <*> newEmptyMVar
  sendMsg (SimChan  s _r) = putMVar  s
  recvMsg (SimChan _s  r) = takeMVar r

data SimChan mvar send recv = SimChan (mvar send) (mvar recv)

flipSimChan (SimChan unichanAB unichanBA) = SimChan unichanBA unichanAB

data SimState g s = SimState {
       runqueue :: ![Thread g s],
       curTime  :: !VTime,
       timers   :: !(PQueue VTime (Action g s)),
       prng     :: !StdGen
     }

--
-- Simulator interpreter
--

type Trace = [(VTime, ThreadId, TraceEvent)]

data TraceEvent = EventFail String
                | EventSay [String]
                | EventTimerCreated VTime
                | EventTimerExpired
                | EventThreadForked ThreadId
                | EventThreadStopped
                | EventCreatedMVar         MVarTag
                | EventNonBlockingTookMVar MVarTag
                | EventFailedTryTakeMVar   MVarTag
                | EventBlockedOnTakeMVar   MVarTag
                | EventUnblockedTakeMVar   MVarTag
                | EventNonBlockingPutMVar  MVarTag
                | EventFailedTryPutMVar    MVarTag
                | EventBlockedOnPutMVar    MVarTag
                | EventUnblockedPutMVar    MVarTag
  deriving Show

type PrngSeed = Int

newProbe :: ST s (SimProbe s a)
newProbe = SimProbe <$> newSTRef []

readProbe :: SimProbe s a -> ST s (ProbeTrace a)
readProbe (SimProbe p) = reverse <$> readSTRef p

runSimM :: forall g . Functor g => PrngSeed -> (forall s. Free (Sum (SimF g SimProbe VTime (SimMVar g s) s) g) ()) -> Trace
runSimM prngseed initialThread = runST (runSimMST prngseed initialThread)

runSimMST :: forall g s. Functor g => PrngSeed -> Free (Sum (SimF g SimProbe VTime (SimMVar g s) s) g) () -> ST s Trace
runSimMST prngseed initialThread = schedule initialState
  where
    initialState :: SimState g s
    initialState = SimState [Thread "main" initialThread]
                            (VTime 0)
                            PQueue.empty
                            (mkStdGen prngseed)

schedule :: forall g s . Functor g => SimState g s -> ST s Trace

-- at least one runnable thread, run it one step
schedule simstate@SimState {
           runqueue = Thread tid action:remaining,
           curTime  = time, timers, prng
         } =
  case action of

    Pure () -> do
      -- this thread is done
      trace <- schedule simstate { runqueue = remaining }
      return ((time,tid,EventThreadStopped):trace)

    Free (InL (Fail msg)) -> do
      -- stop the whole sim on failure
      return ((time,tid,EventFail msg):[])

    Free (InL (Say msg k)) -> do
      let thread' = Thread tid k
      trace <- schedule simstate { runqueue = thread':remaining }
      return ((time,tid,EventSay msg):trace)

    Free (InL (Probe (SimProbe p) o k)) -> do
      modifySTRef p ((time, o):)
      let thread' = Thread tid k
      schedule simstate { runqueue = thread':remaining }

    Free (InL (Timer t a k)) -> do
      let expiry  = t `addTime` time
          timers' = PQueue.insert expiry a timers
          thread' = Thread tid k
      trace <- schedule simstate { runqueue = thread':remaining
                                 , timers   = timers' }
      return ((time,tid,EventTimerCreated expiry):trace)

    Free (InL (Fork a k)) -> do
      let thread'  = Thread tid  k
          tid'     = "TODO"
          thread'' = Thread tid' a
      trace <- schedule simstate { runqueue = thread':thread'':remaining }
      return ((time,tid,EventThreadForked tid'):trace)

    Free (InL (NewEmptyMVar k)) -> do
      v <- newSTRef (MVarEmpty [])
      let vtag    = "TODO"
          thread' = Thread tid (k (SimMVar v vtag))
      trace <- schedule simstate { runqueue = thread':remaining }
      return ((time,tid,EventCreatedMVar vtag):trace)

    Free (InL (PutMVar (SimMVar v vtag) x k)) -> do
      ms <- readSTRef v
      case ms of
        MVarEmpty (t:ts) -> do
          -- there's another thread waiting to take the value, so we pass it
          -- to that thread, wake that thread up, and the MVar remains empty
          writeSTRef v (MVarEmpty ts)
          let thread'  = Thread tid k
              thread''@(Thread tid' _) = t x
          trace <- schedule simstate { runqueue = thread':thread'':remaining }
          return ((time,tid,EventNonBlockingPutMVar vtag)
                 :(time,tid',EventUnblockedTakeMVar vtag):trace)

        MVarEmpty [] -> do
          -- no threads waiting to take the value, so we fill it and move on
          writeSTRef v (MVarFull x [])
          let thread' = Thread tid k
          trace <- schedule simstate { runqueue = thread':remaining }
          return ((time,tid,EventNonBlockingPutMVar vtag):trace)

        MVarFull x0 ts -> do
          -- already full, so we add ourself to the end of the blocked list
          writeSTRef v (MVarFull x0 (ts ++ [(x, Thread tid k)]))
          trace <- schedule simstate { runqueue = remaining }
          return ((time,tid,EventBlockedOnPutMVar vtag):trace)

    Free (InL (TryPutMVar (SimMVar v vtag) x k)) -> do
      ms <- readSTRef v
      case ms of
        MVarEmpty (t:ts) -> do
          -- there's another thread waiting to take the value, so we pass it
          -- to that thread, wake that thread up, and the MVar remains empty
          writeSTRef v (MVarEmpty ts)
          let thread'  = Thread tid (k True)
              thread''@(Thread tid' _) = t x
          trace <- schedule simstate { runqueue = thread':thread'':remaining }
          return ((time,tid,EventNonBlockingPutMVar vtag)
                 :(time,tid',EventUnblockedTakeMVar vtag):trace)

        MVarEmpty [] -> do
          -- no threads waiting to take the value, so we fill it and move on
          writeSTRef v (MVarFull x [])
          let thread' = Thread tid (k True)
          trace <- schedule simstate { runqueue = thread':remaining }
          return ((time,tid,EventNonBlockingPutMVar vtag):trace)

        MVarFull _x0 _ts -> do
          -- already full, but this is non-blocking tryPut so we return
          let thread' = Thread tid (k False)
          trace <- schedule simstate { runqueue = thread':remaining }
          return ((time,tid,EventFailedTryPutMVar vtag):trace)

    Free (InL (TakeMVar (SimMVar v vtag) k)) -> do
      ms <- readSTRef v
      case ms of
        MVarFull x ((x', t):ts) -> do
          -- there's another thread waiting to put a value, so we re-fill the
          -- MVar with that value, and let the other thread go on its way
          writeSTRef v (MVarFull x' ts)
          let thread'  = Thread tid (k x)
              thread''@(Thread tid' _) = t
          trace <- schedule simstate { runqueue = thread':thread'':remaining }
          return ((time,tid,EventNonBlockingTookMVar vtag)
                 :(time,tid',EventUnblockedPutMVar vtag):trace)

        MVarFull x [] -> do
          -- no threads waiting to take the value, so we grab the value and
          -- leave the MVar empty
          writeSTRef v (MVarEmpty [])
          let thread' = Thread tid (k x)
          trace <- schedule simstate { runqueue = thread':remaining }
          return ((time,tid,EventNonBlockingTookMVar vtag):trace)

        MVarEmpty ts -> do
          -- already empty, so we add ourself to the end of the blocked list
          writeSTRef v (MVarEmpty (ts ++ [\x -> Thread tid (k x)]))
          trace <- schedule simstate { runqueue = remaining }
          return ((time,tid,EventBlockedOnTakeMVar vtag):trace)

    Free (InL (TryTakeMVar (SimMVar v vtag) k)) -> do
      ms <- readSTRef v
      case ms of
        MVarFull x ((x', t):ts) -> do
          -- there's another thread waiting to put a value, so we re-fill the
          -- MVar with that value, and let the other thread go on its way
          writeSTRef v (MVarFull x' ts)
          let thread'  = Thread tid (k (Just x))
              thread''@(Thread tid' _) = t
          trace <- schedule simstate { runqueue = thread':thread'':remaining }
          return ((time,tid,EventNonBlockingTookMVar vtag)
                 :(time,tid',EventUnblockedPutMVar vtag):trace)

        MVarFull x [] -> do
          -- no threads waiting to take the value, so we grab the value and
          -- leave the MVar empty
          writeSTRef v (MVarEmpty [])
          let thread' = Thread tid (k (Just x))
          trace <- schedule simstate { runqueue = thread':remaining }
          return ((time,tid,EventNonBlockingTookMVar vtag):trace)

        MVarEmpty _ts -> do
          -- already empty, but this is non-blocking tryTake so we return
          let thread' = Thread tid (k Nothing)
          trace <- schedule simstate { runqueue = thread':remaining }
          return ((time,tid,EventFailedTryTakeMVar vtag):trace)

-- no runnable threads, advance the time to the next timer event, or stop.
schedule simstate@(SimState [] time timers _) =
    -- important to get all events that expire at this time
    case removeMinimums timers of
      Nothing -> return []

      Just (time', events, timers') -> assert (time' > time) $ do
        trace <- schedule simstate { runqueue = map (Thread "timer") events
                                   , curTime  = time'
                                   , timers   = timers' }
        return ((time', "timer", EventTimerExpired):trace)

removeMinimums :: Ord k => PQueue k a -> Maybe (k, [a], PQueue k a)
removeMinimums = \pqueue ->
    case PQueue.minViewWithKey pqueue of
      Nothing                -> Nothing
      Just ((k, x), pqueue') -> Just (collectAll k [x] pqueue')
  where
    collectAll k xs pqueue =
      case PQueue.minViewWithKey pqueue of
        Just ((k', x'), pqueue')
          | k == k' -> collectAll k (x':xs) pqueue'
        _           -> (k, reverse xs, pqueue)

runSimWithSendRecvIO'
    :: forall s a chan .
       (forall x. SimF (SendRecvF chan) IOProbe Microsecond MVar.MVar s x -> IO x)
    -> (forall x. SendRecvF chan x -> IO x)
    -> Free (Sum (SimF (SendRecvF chan) IOProbe Microsecond MVar.MVar s) (SendRecvF chan)) a
    -> IO a
runSimWithSendRecvIO' natSimF natSendRecvF = Free.foldFree nat
    where
    nat :: forall x . Sum (SimF (SendRecvF chan) IOProbe Microsecond MVar.MVar s) (SendRecvF chan) x -> IO x
    nat (InL a) = natSimF a
    nat (InR a) = natSendRecvF a

sumnat
    :: (forall x. f x -> h x)
    -> (forall x. g x -> h x)
    -> Sum f g x -> h x
sumnat lnat _  (InL fx) = lnat fx
sumnat _ rnat  (InR gx) = rnat gx

-- note:
-- if @MonadProbe@ and friends stored the associated type in class
-- variable this function could be generic with a type signagure:
-- @
--  runSimM :: (MonadSay m, MonadProbe m probe, ...) => SimF probe time mvar s a -> m a
-- @
runSimIO
    :: forall g a. Functor g
    => (forall x. g x -> IO x)
    -> SimF g IOProbe Microsecond MVar.MVar Void a -> IO a
runSimIO _ (Fail s)       = fail s
runSimIO _ (Say ss k)     = traverse say ss $> k
runSimIO _ (Probe p o k)  = probeOutput p o $> k
runSimIO nat (Timer t fa k) = timer t (Free.foldFree (sumnat (runSimIO nat) nat) fa) $> k
runSimIO nat (Fork fa k)    = fork (Free.foldFree (sumnat (runSimIO nat) nat) fa) $> k
runSimIO _ (NewEmptyMVar k) = newEmptyMVar >>= return . k
runSimIO _ (TakeMVar v k)   = takeMVar v >>= return . k
runSimIO _ (PutMVar v a k)  = putMVar v a $> k
runSimIO _ (TryTakeMVar v k) = tryTakeMVar v >>= return . k
runSimIO _ (TryPutMVar v a k)  = tryPutMVar v a >>= return . k

runSimWithSendRecvIO
    :: forall a chan .
       (forall x. SendRecvF chan x -> IO x)
    -> Free (Sum (SimF (SendRecvF chan) IOProbe Microsecond MVar.MVar Void) (SendRecvF chan)) a
    -> IO a
runSimWithSendRecvIO nat = runSimWithSendRecvIO' (runSimIO nat) nat

example0 :: (MonadSay m, MonadTimer m, MonadConc m) => m ()
example0 = do
  say "starting"
  v <- newEmptyMVar
  timer 2 $ do
    say "timer fired!"
    putMVar v ()
  say "waiting on mvar"
  takeMVar v
  say "main done"

example1 :: forall s a. [a] -> ST s (Trace, ProbeTrace a)
example1 xs = do
    (p :: SimProbe s a) <- newProbe
    trace <- runSimMST @(Const ()) prngseed $ do
      v <- newEmptyMVar
      return ()
      -- fork (producer v)
      -- fork (consumer v p)
    ptrace <- readProbe p
    return (trace, ptrace)
  where
    prngseed   = 0

    producer :: forall time probe .
                ( Enum (Duration time)
                , TimeMeasure time
                )
             => SimMVar (Const ()) s a
             -> Free (Sum (SimF (Const ()) probe time (SimMVar (Const ()) s) s) (Const ())) ()
    producer v =
      sequence_ [ timer delay $ putMVar v x
                | (delay, x) <- zip [1..] xs ]

    consumer
        :: SimMVar (Const ()) s a
        -> Probe (Free (Sum (SimF (Const ()) probe time (SimMVar (Const ()) s) s) (Const ()))) a
        -> Free (Sum (SimF (Const ()) probe time (SimMVar (Const ()) s) s) (Const ())) ()
    consumer v p = forever $ do
      x <- takeMVar v
      probeOutput p x

example2
  :: forall probe time mvar p c s .
     ( mvar ~ MVar (Free (SimF (SendRecvF (SimChan mvar)) probe time mvar s))
     , BiChan (Free (SimF (SendRecvF (SimChan mvar)) probe time mvar s)) ~ SimChan mvar
     , Enum (Duration (Time (Free (SimF (SendRecvF (SimChan mvar)) probe time mvar s))))
     , MonadTimer (Free (SimF (SendRecvF (SimChan mvar)) probe time mvar s))
     )
  => TestChainAndUpdates
  -> Free (Sum (SimF (SendRecvF (SimChan mvar)) probe time mvar s) (SendRecvF (SimChan mvar))) ()
example2 (TestChainAndUpdates _c us) = do
    chainvar <- Free.liftF $ InL (NewEmptyMVar id)
    hoistFree InL $ fork $ generator chainvar us
    simulateWire (producer chainvar) consumer
  where
    generator chainvar us =
      sequence_
        [ timer d $ do
            case u of
              AddBlock b -> putMVar chainvar (RollForward b)
              SwitchFork _n bs -> do
                putMVar chainvar (RollBackward (0, 0)) --TODO dummy
                mapM_ (putMVar chainvar . RollForward) bs
        | (d, u) <- zip [1..] us ]

    producer :: mvar (ConsumeChain Block)
             -> SimChan mvar MsgProducer MsgConsumer
             -> Free (Sum (SimF (SendRecvF (SimChan mvar)) probe time mvar s) (SendRecvF (SimChan mvar))) ()
    producer chainvar =
      producerSideProtocol1
        (\_rid -> tryTakeMVar chainvar)
        (\_rid -> takeMVar chainvar)
        0 --TODO: dummy rid

    consumer :: SimChan mvar MsgConsumer MsgProducer
             -> Free (Sum (SimF (SendRecvF (SimChan mvar)) probe time mvar s) (SendRecvF (SimChan mvar))) ()
    consumer =
      consumerSideProtocol1
        (\b -> say ("addBlock " ++ show b))
        (\p -> say ("rollBackTo " ++ show p))

--
-- STM based protocol
--

-- | An STM-based interface provided by a chain producer to chain consumers.
--
data ChainProducer = ChainProducer {
       establishChainConsumer :: [Point]
                              -> STM (ChainConsumer, [Point])
     }

data ChainConsumer = ChainConsumer {
       currentReadPoint :: STM Point,
       improveReadPoint :: [Point] -> STM (),
       tryPeekChain     :: STM (Maybe (ConsumeChain Block)),
       tryReadChain     :: STM (Maybe (ConsumeChain Block))
     }

type MaxReadBlocks = Int

readRollForwardOnly :: ChainConsumer -> MaxReadBlocks -> STM [Block]
readRollForwardOnly ChainConsumer{tryPeekChain, tryReadChain} maxBlocks =
    go maxBlocks
  where 
    go 0 = return []
    go n = do
      res <- tryPeekChain
      case res of
        Just (RollForward b) -> do
          _ <- tryReadChain
          bs <- go (n-1)
          return (b:bs)
        _ -> return []

-- | Like 'tryReadChain' but reads multiple blocks in one go.
--
tryReadChainN :: ChainConsumer
              -> MaxReadBlocks -- ^ The maximum number of blocks to read
              -> STM (Maybe (ConsumeChain [Block]))
tryReadChainN cs@ChainConsumer{..} maxBlocks = do
    res <- tryReadChain
    case res of
      -- If we're at the chain head or it's a rollback we just return that.
      Nothing               -> return Nothing
      Just (RollBackward p) -> return (Just (RollBackward p))
      -- If we get one block we peek at what's ahead and consume any
      -- more blocks, up to our limit.
      Just (RollForward b) -> do
        bs <- readRollForwardOnly cs (maxBlocks-1)
        return (Just (RollForward (b:bs)))

-- | Like 'tryReadChainN' but blocks at the chain head.
--
readChainN :: ChainConsumer
           -> MaxReadBlocks -- ^ The maximum number of blocks to read
           -> STM (ConsumeChain [Block])
readChainN cs@ChainConsumer{..} maxBlocks = do
    res <- tryReadChain
    case res of
      -- If it's the chain head we block by retrying.
      Nothing                 -> retry
      -- If it's a rollback we just return that.
      Just (RollBackward p) -> return (RollBackward p)
      -- If we get one block we peek at what's ahead and consume any
      -- more blocks, up to our limit.
      Just (RollForward b) -> do
        bs <- readRollForwardOnly cs (maxBlocks-1)
        return (RollForward (b:bs))

