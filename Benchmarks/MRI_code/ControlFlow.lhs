> {-# LANGUAGE FlexibleContexts #-}

> module ControlFlow where

> import Data.Map
> import Control.Monad.State
> import Control.Monad.Identity
> import Control.Monad.Writer
> import Advice

REPLACEMENT

> type Replace s = s
>
> replace :: Replace s -> Open s
> replace radv  = \super -> radv

AUGMENTATION

> type Augment a b c m = (a -> m c, a -> b -> c -> m ())
>
> augment  :: Monad m => Augment a b c m -> Open (a -> m b)
> augment (bef,aft) super a = 
>   do {c <- bef a; b <- super a; aft a b c; return b}

> log'  :: (MonadWriter String m, Show a, Show b) => String -> Augment a b () m
> log' name = (bef,aft) where 
>    bef x        = write "Entering " x 
>    aft _ y _    = write "Exiting "  y
>    write a b  = tell (a ++ name ++ show b ++ "\n" )

> before  :: Monad m => (a -> m ())      -> Open (a -> m b)
> after   :: Monad m => (a -> b -> m ()) -> Open (a -> m b)
>
> before bef = augment (\a -> bef a >> return (), \a b c -> return ())
> after  aft = augment (\_ -> return (), \a b c -> aft a b)

> dump' :: (MonadState s m, MonadWriter String m, Show s) => a -> m ()
> dump' arg = do  s <- get 
>                 tell (show s ++ "\n")

NARROWING

> type Narrow a b c m = (a -> m Bool, Augment a b c m, Replace (a -> m b))
>
> narrow ::  Monad m => Narrow a b c m -> Open (a -> m b)
> narrow (p,aug,rep) super x =
>    do  b <- p x
>        if b  then replace rep super x
>              else augment aug super x

> memo1 :: (MonadState (Map a b) m, Ord a) => Narrow a b () m
> memo1 = (p,(bef, aft),rep) where
>   p x        = do { m <- get ; return (member x m) }
>   bef _      = return () 
>   aft x r _  = do { m <- get ; put (insert x r m) }
>   rep x      = do { m <- get ; return (m ! x) }
