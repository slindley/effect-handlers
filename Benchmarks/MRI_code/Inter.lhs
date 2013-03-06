> {-# LANGUAGE NoMonomorphismRestriction #-}
> {-# LANGUAGE FlexibleContexts #-}

> module Mechanisms where

> import Control.Monad.Writer
> import Advice hiding (fib2)
> import Effects (fib2)

> logfib = new (log <@> fib2)
>   where 
>    log :: MonadWriter String m => Open (Int -> m Int)
>    log super n = do  tell "entering fib"
>                      super n
>
