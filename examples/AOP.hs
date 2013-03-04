{- Aspect-oriented programming using handlers.

Inspired by Oliveira, Shrijvers, and Cook's JFP paper: Modular
reasoning about interference in incremental programming -}

{-# LANGUAGE TypeFamilies,
    GADTs,
    NoMonomorphismRestriction,
    RankNTypes,
    MultiParamTypeClasses,
    QuasiQuotes,
    FlexibleInstances,
    FlexibleContexts,
    OverlappingInstances,
    UndecidableInstances,
    ConstraintKinds,
    DataKinds,
    PolyKinds,
    TypeOperators,
    ScopedTypeVariables #-}

module AOP where

import Handlers
import TopLevel
import DesugarHandlers

import Control.Monad
import Data.Monoid

[operation|Get s :: s|]
[operation|Put s :: s -> ()|]

[operation|Ask s :: s|]
[operation|Tell s :: s -> ()|]

type SComp s a =
  forall h.(  [handles|h {Get s}|],
              [handles|h {Put s}|]) => Comp h a

[handler|
  forward h.
    RunState s a :: s -> (a, s)
      handles {Get s, Put s} where
        Return  x     s -> return (x, s)
        Get        k  s -> k s  s
        Put     s  k  _ -> k () s
|] 
[handler| 
  forward h.
    EvalState s a :: s -> a 
      handles {Get s, Put s} where
        Return  x     _ -> return x
        Get        k  s -> k s  s
        Put     s  k  _ -> k () s
|]


[handler|
  forward h.
    RunReader s a :: s -> a
      handles {Ask s} where
        Return  x     s -> return x
        Ask        k  s -> k s  s
|] 

[handler| 
  forward h.(Monoid s) =>
    RunWriter s a :: s -> (a, s)
      handles {Tell s} where
        Return  x      s -> return (x, s)
        Tell    s'  k  s -> k () (s `mappend` s')
|]
runWriter' comp = runWriter mempty comp
[handler|
  forward h.(Monoid s) =>
    EvalWriter s a :: s -> a
      handles {Tell s} where
        Return  x      _ -> return x
        Tell    s'  k  s -> k () (s `mappend` s')
|]
evalWriter' comp = evalWriter mempty comp
[handler|
  IoStringWriter a :: IO a
    handles {Tell (String)} where
      Return  x     -> return x
      Tell    s   k -> do putStr s; k ()
|]


[handler| 
  forward h.(Monoid s) =>
    ExecWriter s a :: s -> s
      handles {Tell s} where
        Return  x      s -> return s
        Tell    s'  k  s -> k () (s `mappend` s')
|]
execWriter' comp = execWriter mempty comp

[operation|forall a.ThrowError e :: e -> a|]
[handler|
  forward h.
    CatchError e a :: (e -> Comp h a) -> a
      handles {ThrowError e} where
        Return x       _ -> return x
        ThrowError e k f -> f e
|]
[handler|
  forward h.
    RunError e a :: Either e a
      handles {ThrowError e} where
        Return x       -> return (Right x)
        ThrowError e k -> return (Left e)
|]


data Expr
  = Lit Int
  | Var String
  | Plus Expr Expr
  | Assign String Expr
  | Sequence [Expr]
  | While Expr Expr
  deriving Show
type Env = [(String, Int)]

[operation|Suspend h s a :: s -> Comp h a -> a|]
bevalStep :: ([handles|h {Get (Env)}|],
              [handles|h {Put (Env)}|],
              [handles|h {Suspend h (Expr) (Int)}|]) =>
                Expr -> Comp h Int
bevalStep exp = case exp of
  Lit x           -> return x
  Var s           -> do e <- get
                        case lookup s e of
                          Just x -> return x
                          _      -> error "Variable not found!"
  Plus l r        -> do x <- beval l
                        y <- beval r
                        return (x+y)
  Assign x r      -> do y <- beval r
                        e <- get
                        put ((x, y) : e)
                        return y
  Sequence []     -> return 0
  Sequence [x]    -> beval x
  Sequence (x:xs) -> beval x >> beval (Sequence xs)
  While c b       -> do x <- beval c
                        if x == 0 then return 0
                                  else (beval b >> beval exp)
beval :: ([handles|h {Get (Env)}|],
          [handles|h {Put (Env)}|],
          [handles|h {Suspend h (Expr) (Int)}|]) =>
            Expr -> Comp h Int
beval e = suspend e (bevalStep e)

[handler|
  forward h.
    Force a :: a
      handles {Suspend (Force h a) s a} where
        Return x         -> return x
        Suspend e comp k -> do x <- force comp; k x
|]

[handler|
  forward h handles {Tell (String), Suspend h s a}.(Show s, Show a) =>
    Logger a :: String -> a
      handles {Suspend (Logger h a) s a} where
        Return x              _    -> return x
        Suspend e comp    k   name -> do tell ("Entering " ++ name ++ " with " ++ show e ++ "\n")
                                         y <- suspend e (logger name comp)
                                         tell ("Exiting " ++ name ++ " with " ++ show y ++ "\n")
                                         k y name
|]

[handler|
  forward h handles {Get s, Tell (String), Suspend h t a}.(Show s) =>
    Dump s a :: a
      handles {Suspend (Dump h s a) t a} where
        Return x         -> return x
        Suspend e comp k -> do s <- get
                               tell (show s ++ "\n")
                               x <- suspend e (dump comp)
                               k x
|]

e1 = Plus (Lit 3) (Lit 4)
e2 = Plus (Assign "x" (Lit 3)) (Assign "y" (Lit 4))
e3 = Plus (Plus (Assign "x" (Lit 3)) (Assign "y" (Lit 4))) (Plus (Var "x") (Var "y"))

test1 e = ioStringWriter (evalState [] (force (logger "eval" (beval e))))
test2 e = ioStringWriter (evalState [] (force (dump (beval e))))
test3 e = ioStringWriter (evalState [] (force (dump (logger "eval" (beval e)))))

