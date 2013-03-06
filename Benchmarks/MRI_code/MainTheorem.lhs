> {-# LANGUAGE RankNTypes #-}

> module MainTheorems where

> import Control.Monad.State
> import Control.Monad.Identity
> import Control.Monad.Writer
> import Advice
> import Interference
> import ControlFlow


HARMLESS MIXINS

> type NIAugment a b c t = forall m. (Monad m, Monad (t m)) => Augment a b c (t m) 

> (@@) :: (Monad m, MonadTrans t, Monad (t m)) => 
>  NIAugment a b c t -> NIBase a b m -> Open (a -> t m b)
> adv @@ bse = augment adv `orthogonal` bse

> convert :: (Monad m, MonadTrans t, Monad (t m))
>   => (a -> t m c, a -> b -> c -> t m ()) 
>   -> (a -> t m (b -> t m ()))
> convert (bef,aft)  = 
>   \a -> bef a >>= (\c -> return (\b -> aft a b c))

> around :: (Monad m, MonadTrans t, Monad (t m))
>   => (a -> t m (b -> t m ()))
>   -> Open (a -> t m b)
> around adv = \super ->
>   \a -> adv a       >>= \aft -> 
>         super a   >>= \r   ->
>         aft r       >>= \_   ->
>         return r


PROJECTION FUNCTIONS

> projW :: forall w m a. (Monad m, Monoid w) => WriterT w m a -> m a
> projW m  = runWriterT m >>= return . fst

> projS :: forall s m a. Monad m => s -> StateT s m a -> m a
> projS s0 m  = runStateT m s0 >>= return . fst


HARMLESS OBSERVATION MIXINS

> type NIOAugment a b c s t = forall m. (MonadGet s m, Monad (t m)) => Augment a b c (t m)
>
> (@-@) :: (MonadGet s m, MonadTrans t, MonadGet s (t m)) => 
>   NIOAugment a b c s t -> NIBase a b m -> Open (a -> t m b)
> adv @-@ bse = augment adv `observation` bse
