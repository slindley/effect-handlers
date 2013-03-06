> {-# LANGUAGE NoMonomorphismRestriction #-}
> {-# LANGUAGE NPlusKPatterns #-}

> module ModularReasoning where
>
> import Control.Monad.State
> import Control.Monad.Reader

> tick = get >>= put . (+1)

> type M1 = State Int ()
> type M2 = StateT  Int (Reader String) ()
> type M3 = ReaderT String (State Int) ()

> hanoi 0      = return ()
> hanoi (n+1)  = hanoi n >> tick >> hanoi n
>
> rep 0      mx    = return ()
> rep (n+1)  mx    = mx >> rep n mx
