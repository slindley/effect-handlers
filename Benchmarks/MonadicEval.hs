-- hardcoded evaluator with logging and environment dumping

module Benchmarks.MonadicEval where

import Control.Monad.State
import Control.Monad.Writer

import Benchmarks.MRI_code.Interpreters (Expr(..), Env)

eval :: Expr -> StateT Env (Writer String) Int
eval exp =
  do s <- get
     tell (show s ++ "\n")
     tell ("Entering eval with" ++ show exp ++ "\n")  
     result <-
       case exp of 
         Lit x             -> return x
         Var s             -> do  e <- get
                                  case lookup s e of 
                                    Just x  -> return x
                                    _       -> error "Variable not found!"
         Plus l r          -> do  x <- eval l
                                  y <- eval r
                                  return (x+y)
         Assign x r        -> do  y <- eval r
                                  e <- get
                                  put ((x,y):e)
                                  return y
         Sequence []       -> return 0
         Sequence [x]      -> eval x
         Sequence (x:xs)   -> eval x >> eval (Sequence xs)
         While c b         -> do  x <- eval c
                                  if (x == 0) then return 0
                                    else (eval b >> eval exp)
     tell ("Exiting eval with" ++ show result ++ "\n")
     return result

logdumptest e = execWriter (runStateT (eval e) [])
