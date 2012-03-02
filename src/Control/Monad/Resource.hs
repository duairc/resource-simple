{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{-|

Allocate resources which are guaranteed to be released.

One point to note: all register cleanup actions live in IO, not the main
monad. This allows both more efficient code, and for monads to be transformed.

-}

module Control.Monad.Resource
    (  -- * The @ResourceT@ monad transformer
      ResourceT
      -- ** Running
    , runResourceT
      -- ** Monad transformation
    , mapResourceT
      -- * The @MonadResource@ type class
    , MonadResource (..)
    , ReleaseKey
    )
where

import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import           Data.IORef (IORef, newIORef, writeIORef, atomicModifyIORef)
import           Data.Word (Word)
import           Control.Applicative (Applicative (..), Alternative (..))
import           Control.Exception (SomeException, mask, mask_, try, finally)
import           Control.Monad (MonadPlus (..), ap, liftM, when)
import           Control.Monad.Base (MonadBase (..))
import           Control.Monad.Fork.Class (MonadFork (..))
import           Control.Monad.Instances.Evil ()
import           Control.Monad.IO.Class (MonadIO)
import           Control.Monad.Trans.Class (MonadTrans (..))
import           Control.Monad.Trans.Control
                     ( MonadBaseControl (..)
                     , MonadTransControl (..)
                     , control
                     )


------------------------------------------------------------------------------
-- | A lookup key for a specific release action. This value is returned by
-- 'register' and 'with' and is passed to 'release'.
newtype ReleaseKey = ReleaseKey Int


------------------------------------------------------------------------------
data ReleaseMap = ReleaseMap !Int !Word !(IntMap (IO ()))


------------------------------------------------------------------------------
-- | The Resource transformer. This transformer keeps track of all registered
-- actions, and calls them upon exit (via 'runResourceT'). Actions may be
-- registered via 'register', or resources may be allocated atomically via
-- 'with'. The 'with' function corresponds closely to @bracket@. These
-- functions are provided by 'ResourceT'\'s 'MonadResource' instance.
--
-- Releasing may be performed before exit via the 'release' function. This is
-- a highly recommended optimization, as it will ensure that scarce resources
-- are freed early. Note that calling @release@ will deregister the action, so
-- that a release action will only ever be called once.
--
-- Pass-through instances for the @mtl@ type classes are provided
-- automatically by the @mtl-evil-instances@ package.
newtype ResourceT m a = ResourceT (IORef ReleaseMap -> m a)


------------------------------------------------------------------------------
instance MonadTrans ResourceT where
    lift = ResourceT . const


------------------------------------------------------------------------------
instance MonadTransControl ResourceT where
    newtype StT ResourceT a = StReader {unStReader :: a}
    liftWith f = ResourceT $ \r -> f $ \(ResourceT t) -> liftM StReader $ t r
    restoreT = ResourceT . const . liftM unStReader


------------------------------------------------------------------------------
instance Monad m => Functor (ResourceT m) where
    fmap = liftM


------------------------------------------------------------------------------
instance Monad m => Applicative (ResourceT m) where
    pure = return
    (<*>) = ap


------------------------------------------------------------------------------
instance MonadPlus m => Alternative (ResourceT m) where
    empty = mzero
    (<|>) = mplus


------------------------------------------------------------------------------
instance Monad m => Monad (ResourceT m) where
    return = ResourceT . const . return
    ResourceT m >>= f = ResourceT $ \r -> m r >>= \a ->
        let ResourceT m' = f a in m' r


------------------------------------------------------------------------------
instance MonadPlus m => MonadPlus (ResourceT m) where
    mzero = ResourceT $ const mzero
    mplus (ResourceT m) (ResourceT m') = ResourceT $ \r -> mplus (m r) (m' r)


------------------------------------------------------------------------------
instance MonadBaseControl b m => MonadBaseControl b (ResourceT m) where
     newtype StM (ResourceT m) a = StMT (StM m a)
     liftBaseWith f = ResourceT $ \reader ->
         liftBaseWith $ \runInBase ->
             f $ liftM StMT . runInBase . (\(ResourceT r) -> r reader)
     restoreM (StMT base) = ResourceT $ const $ restoreM base


------------------------------------------------------------------------------
instance (MonadFork m, MonadBaseControl IO m) => MonadFork (ResourceT m) where
    fork (ResourceT f) = ResourceT $ \istate ->
        control $ \run -> mask $ \unmask -> do
            stateAlloc istate
            run . fork $ control $ \run' -> do
                unmask (run' $ f istate) `finally` stateCleanup istate


------------------------------------------------------------------------------
-- | Transform the monad a @ResourceT@ lives in. This is most often used to
-- strip or add new transformers to a stack, e.g. to run a @ReaderT@.
mapResourceT :: (m a -> n b) -> ResourceT m a -> ResourceT n b
mapResourceT f (ResourceT m) = ResourceT $ f . m


------------------------------------------------------------------------------
-- | Unwrap a 'ResourceT' transformer, and call all registered release
-- actions.
--
-- Note that there is some reference counting involved due to the
-- implementation of 'fork' used in the 'MonadFork' instance. If multiple
-- threads are sharing the same collection of resources, only the last call
-- to @runResourceT@ will deallocate the resources.
runResourceT :: MonadBaseControl IO m => ResourceT m a -> m a
runResourceT (ResourceT r) = do
    istate <- liftBase $ newIORef $ ReleaseMap 0 0 IntMap.empty
    control $ \run -> mask $ \unmask -> do
        stateAlloc istate
        unmask (run $ r istate) `finally` stateCleanup istate


------------------------------------------------------------------------------
stateAlloc :: IORef ReleaseMap -> IO ()
stateAlloc istate = atomicModifyIORef istate $ \(ReleaseMap key ref im) ->
    (ReleaseMap key (ref + 1) im, ())


------------------------------------------------------------------------------
stateCleanup :: IORef ReleaseMap -> IO ()
stateCleanup istate = mask_ $ do
    (ref, im) <- atomicModifyIORef istate $ \(ReleaseMap key ref im) ->
        (ReleaseMap key (ref - 1) im, (ref - 1, im))
    when (ref == 0) $ do
        mapM_ (\x -> try' x >> return ()) $ IntMap.elems im
        writeIORef istate $ error "Control.Monad.Resource.stateCleanup: There\
            \ is a bug in the implementation. The mutable state is being\
            \ accessed after cleanup. Please contact the maintainers."
  where
    try' = try :: IO a -> IO (Either SomeException a)


------------------------------------------------------------------------------
register' :: IORef ReleaseMap -> IO () -> IO ReleaseKey
register' istate m = atomicModifyIORef istate $ \(ReleaseMap key ref im) ->
    (ReleaseMap (key + 1) ref (IntMap.insert key m im), ReleaseKey key)


------------------------------------------------------------------------------
release' :: IORef ReleaseMap -> ReleaseKey -> IO ()
release' istate (ReleaseKey key) = mask $ \unmask -> do
    atomicModifyIORef istate lookupAction >>= maybe (return ()) unmask
  where
    lookupAction rm@(ReleaseMap key' ref im) =
        case IntMap.lookup key im of
            Nothing -> (rm, Nothing)
            Just m -> (ReleaseMap key' ref $ IntMap.delete key im, Just m)


------------------------------------------------------------------------------
-- | The 'MonadResource' type class. This provides the 'with', 'register' and
-- 'release' functions, which are the main functionality of this package. The
-- main instance of this class is 'ResourceT'.
--
-- The others instances are overlapping instances (in the spirit of
-- @mtl-evil-instances@), which provide automatic pass-through instances for
-- 'MonadResource' for every monad transformer. This means that you don't have
-- to provide a pass-through instance of 'MonadResource' for every monad
-- transformer you write.
class MonadIO m => MonadResource m where
    -- | Perform some allocation, and automatically register a cleanup action.
    with :: IO a -> (a -> IO ()) -> m (ReleaseKey, a)

    -- | Register some action that will be run precisely once, either when
    -- 'runResourceT' is called, or when the 'ReleaseKey' is passed to
    -- 'release'.
    register :: IO () -> m ReleaseKey

    -- | Call a release action early, and deregister it from the list of
    -- cleanup actions to be performed.
    release :: ReleaseKey -> m ()


------------------------------------------------------------------------------
instance MonadBaseControl IO m => MonadResource (ResourceT m) where
    with acquire m = ResourceT $ \istate -> liftBase . mask $ \unmask -> do
        a <- unmask acquire
        key <- register' istate $ m a
        return (key, a)
    register m = ResourceT $ \istate -> liftBase $ register' istate m
    release key = ResourceT $ \istate -> liftBase $ release' istate key


------------------------------------------------------------------------------
instance (MonadTrans t, Monad (t m), MonadResource m) => MonadResource (t m) where
    with = (lift .) . with
    register = lift . register
    release = lift . release


------------------------------------------------------------------------------
instance (MonadBase b m, MonadResource b) => MonadResource m where
    with = (liftBase .) . with
    register = liftBase . register
    release = liftBase . release
