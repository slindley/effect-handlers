> {-# LANGUAGE TypeSynonymInstances #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE FlexibleInstances #-}

> module Benchmarks.MRI_code.Interpreters where
>
> import Prelude hiding (log, exp)
> import Data.List hiding (insert)
> import Control.Monad.State
> import Control.Monad.Writer
> import Control.Monad.Identity
> import Control.Applicative hiding (empty)
> import Data.Traversable hiding (mapM)
> import Benchmarks.MRI_code.Advice 
> import Benchmarks.MRI_code.Effects hiding (evalState)
> import Data.Map hiding (lookup,map)
> import Control.Monad.Error


> data Expr  
>   = Lit Int
>   | Var String
>   | Plus Expr Expr
>   | Assign String Expr
>   | Sequence [Expr]
>   | While Expr Expr
>   deriving Show
>
> type Env = [(String, Int)]

> beval :: MonadState Env m => Open (Expr -> m Int)
> beval this exp = case exp of 
>   Lit x             -> return x
>   Var s             -> do  e <- get
>                            case lookup s e of 
>                              Just x  -> return x
>                              _       -> error msg
>   Plus l r          -> do  x <- this l
>                            y <- this r
>                            return (x+y)
>   Assign x r        -> do  y <- this r
>                            e <- get
>                            put ((x,y):e)
>                            return y
>   Sequence []       -> return 0
>   Sequence [x]      -> this x
>   Sequence (x:xs)   -> this x >> this (Sequence xs)
>   While c b         -> do  x <- this c
>                            if (x == 0) then return 0
>                              else (this b >> this exp)
>   where msg = "Variable not found!"

> eval :: Expr -> State Env Int
> eval = new beval

> -- the logging mixin
> log :: (MonadWriter String m, Show a, Show b) => String -> Open (a -> m b)
> log name super x =  do
>   tell ("Entering " ++ name ++ "with" ++ show x ++ "\n")
>   y <- super x
>   tell ("Exiting " ++ name ++ "with" ++ show y ++ "\n")
>   return y
>
> -- the environment dumping mixin 
> dump :: (MonadState s m, MonadWriter String m, Show s) => Open (a -> m b)
> dump super arg = do  s <- get 
>                      tell (show s ++ "\n")
>                      super arg 
>
> -- the exception handling mixin
> type Exc = (String,Expr,Env)
> instance Error Exc
>
> eeval ::  (MonadState Env m, MonadError Exc m) => Open (Expr -> m Int)
> eeval super exp = case exp of
>   Var s  -> do  e <- get 
>                 case lookup s e of 
>                   Just x  -> return x
>                   _       -> throwError (msg,exp,e) 
>   _      -> super exp
>   where msg = "Variable not found!"

> teval :: MonadWriter String m => Open (Expr -> m Int)
> teval super exp = case exp of 
>   While c b  ->  
>     do n <- teval super c
>        if (n == 0) then (tell "done\n" >> return 0)
>                    else (tell "repeating\n"  >> teval super b 
>                                              >> teval super exp)
>   _          -> super exp

> debug1, debug2 :: (MonadWriter String m, MonadState Env m) => Expr -> m Int
> debug1 = new (log "eval" <@> beval)
> debug2 = new (log "eval" <@> dump <@> beval)

> exc ::  (MonadError Exc m, MonadWriter String m, MonadState Env m) => Expr -> m Int
> exc = new (eeval <@> log "eval" <@> beval)

> test1 e = evalState (execWriterT (debug1 e)) []
>
> test2 e = evalState (execWriterT (debug2 e)) []
>
> test3 e = extract (evalStateT (execWriterT (exc e)) [])
>   where
>     extract (Left (msg,exp,_))  =  "Error: " ++ msg ++ 
>                                    "\nIn Expression: " ++ show exp
>     extract (Right t)           =  t
