> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FunctionalDependencies #-}
> {-# LANGUAGE FlexibleContexts #-}

> module Interference where

> import Data.Map
> import Control.Monad.State hiding (get)
> import Control.Monad.Writer
> import Advice 
> import Effects
> import Interpreters
> import ControlFlow


INTERFERENCE PRIMITIVES

> type NIMixin a b t = forall m. (Monad m, Monad (t m)) => Open (a -> t m b)
>
> nimixin :: (Monad m, MonadTrans t, Monad (t m)) => NIMixin a b t -> Open (a -> t m b)
> nimixin mix = mix

> type NIBase a b m = forall t. (MonadTrans t, Monad (t m)) => Open (a -> t m b)
>
> nibase :: (Monad m, MonadTrans t, Monad (t m)) => NIBase a b m -> Open (a -> t m b)
> nibase bse = bse 

> log'' :: (Show a, Show b) => NIMixin a b (WriterT String)
> log'' = augment (log' "eval")


INTERFERENCE COMBINATORS

> orthogonal     :: (MonadTrans t, Monad m, Monad (t m)) 
>                => NIMixin a b t -> NIBase a b m -> Open (a -> t m b)
> mix `orthogonal` bse = nimixin mix <@> nibase bse
>
> actuation'     :: (MonadTrans t, Monad m, Monad (t m))
>                => Open (a -> t m b) -> NIBase a b m -> Open (a -> t m b)
> mix `actuation'` bse = mix <@> nibase bse 
>
> inv_actuation  :: (MonadTrans t, Monad m, Monad (t m))
>                => NIMixin a b t -> Open (a -> t m b) -> Open (a -> t m b)
> mix `inv_actuation` bse = nimixin mix <@> bse
>
> interference   :: (MonadTrans t, Monad m, Monad (t m))
>                => Open (a -> t m b) -> Open (a -> t m b) -> Open (a -> t m b)
> mix `interference` bse = mix <@> bse


STATEFUL EFFECTS

> class Monad m => MonadGet s m | m -> s where
>   get :: m s 
>
> class Monad m => MonadPut s m | m -> s where
>   put :: s -> m ()
>
> class (MonadGet s m, MonadPut s m) => MonadState s m

> dump'' :: (MonadGet s m, MonadWriter String m, Show s) => a -> m ()
> dump'' _ = do {s <- get ; tell (show s ++ "\n")}

> type ROAdvice a b t s  = forall m. (MonadGet s m, MonadGet s (t m)) => Open (a -> t m b)
>
> type WOAdvice a b t s  = forall m. (MonadPut s m, MonadPut s (t m)) => Open (a -> t m b) 

> dump''' :: Show s => ROAdvice a b (WriterT String) s
> dump''' = before dump''

> observation :: (MonadGet s m, MonadGet s (t m), MonadTrans t) => 
>   ROAdvice a b t s -> NIBase a b m -> Open (a -> t m b)
> observation mix bse = mix <@> bse
>
> actuation :: (MonadPut s m, MonadPut s (t m), MonadTrans t) =>
>   WOAdvice a b t s -> NIBase a b m -> Open (a -> t m b)
> actuation mix bse = mix <@> bse
