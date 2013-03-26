{- Aspect-oriented programming using handlers.

Inspired by Oliveira, Shrijvers, and Cook's JFP paper: Modular
reasoning about interference in incremental programming -}

{- This version supports overriding the behaviour of a function on a
particular expression constructor by reflecting each expression
constructor as an effectful operation and defining functions on
expressions as handlers. -}

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

module AOPExtra where

import Handlers
import TopLevel
import DesugarHandlers

import Control.Monad
import Data.Monoid

import Benchmarks.MRI_code.Interpreters (Expr(..), Env)

[operation|Get s :: s|]
[operation|Put s :: s -> ()|]

[operation|Ask s :: s|]
[operation|Tell s :: s -> ()|]

type SComp s a =
  ((h `Handles` Get) s, (h `Handles` Put) s) => Comp h a

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

-- data Expr
--   = Lit Int
--   | Var String
--   | Plus Expr Expr
--   | Assign String Expr
--   | Sequence [Expr]
--   | While Expr Expr
--   deriving Show
-- type Env = [(String, Int)]

-- the representation of an expression as a computation
type ExprComp a =
  ([handles|h {CLit}|],
   [handles|h {CVar}|],
   [handles|h {CPlus}|],
   [handles|h {CAssign}|],
   [handles|h {CSequence}|],
   [handles|h {CWhile}|]) => Comp h a

[operation|forall a.CLit      :: Int    -> a   |]
[operation|forall a.CVar      :: String -> a   |]
[operation|         CPlus     ::           Bool|]
[operation|         CAssign   :: String -> ()  |]
[operation|         CSequence :: Int    -> Int |]
[operation|         CWhile    ::           Bool|]

-- effectful smart constructors
lit = cLit
var = cVar
plus e1 e2 = do b <- cPlus; if b then e1 else e2
assign x e = do cAssign x; e
sequence' es = do i <- cSequence (length es); es !! i
while e1 e2 = do b <- cWhile; if b then e1 else e2


[operation|Suspend h s a :: s -> Comp h a -> a|]
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


type ExprSuspendComp a =
  ([handles|h {CLit}|],
   [handles|h {CVar}|],
   [handles|h {CPlus}|],
   [handles|h {CAssign}|],
   [handles|h {CSequence}|],
   [handles|h {CWhile}|],
   [handles|h {Suspend h (Expr) a}|]) => Comp h a


-- we won't use this, but we can pretty print reflected expressions
-- using a handler
[handler|
  forward h handles {Tell (String)}.
    ShowExpr :: ()
      handles {CLit, CVar, CPlus, CAssign, CSequence, CWhile} where
        Return x       -> tell (show x)
        CLit x       k -> tell (show x)
        CVar s       k -> tell s
        CPlus        k -> do tell "("
                             k True
                             tell ")+("
                             k False
                             tell ")"
        CAssign s    k -> do tell (s ++ ":=(")
                             k ()
                             tell ")"
        CSequence n  k -> do tell "["
                             loop n
                             tell "]"
                             where loop 0 = return ()
                                   loop 1 = k 0
                                   loop n = do k (n-1); tell ","
        CWhile       k -> do tell "while "
                             k True
                             tell " do "
                             k False
|]
showExpr' :: ([handles|h {Tell (String)}|], Show a) => ExprComp a -> Comp h ()
showExpr' comp = showExpr comp


-- similarly to pretty-printing, we can reify reflected expressions as
-- plain expressions
[handler|
  forward h.
    Reify :: Expr
      handles {CLit, CVar, CPlus, CAssign, CSequence, CWhile} where
        Return x       -> return (Lit x)
        CLit x       k -> return (Lit x)
        CVar s       k -> return (Var s)
        CPlus        k -> do l <- k True; r <- k False; return (Plus l r)
        CAssign s    k -> do e <- k (); return (Assign s e)
        CSequence n  k -> do es <- loop n
                             return (Sequence es)
                             where loop 0 = return []
                                   loop n = do e <- k (n-1); es <- loop (n-1); return (e:es)
        CWhile       k -> do c <- k True; b <- k False; return (While c b)
|]

-- reflect an expression
reflect :: Expr -> ExprComp a
reflect (Var s) = var s
reflect (Lit x) = lit x
reflect (Plus e1 e2) = plus (reflect e1) (reflect e2)
reflect (Assign x r) = assign x (reflect r)
reflect (Sequence es) = sequence' (map reflect es)
reflect (While c b) = while (reflect c) (reflect b)

-- reflect an expression by 'suspending' each constructor
-- this provides a hook to support aspect-oriented programming
reflectSuspend :: Expr -> ExprSuspendComp a
reflectSuspend (Var s) = suspend (Var s) (var s)
reflectSuspend (Lit x) = suspend (Lit x) (lit x)
reflectSuspend (Plus e1 e2) = suspend (Plus e1 e2) (plus (reflectSuspend e1) (reflectSuspend e2))
reflectSuspend (Assign x r) = suspend (Assign x r) (assign x (reflectSuspend r))
reflectSuspend (Sequence es) = suspend (Sequence es) (sequence' (map reflectSuspend es))
reflectSuspend (While c b) = suspend (While c b) (while (reflectSuspend c) (reflectSuspend b))

-- We could separate reflection from the introduction of suspended
-- computations, but filling in the annotations on each suspended node
-- would probably require us to reify computations, which might be
-- undesirable.
--
-- [handler|
--   forward h handles {Suspend h (Expr) (Int), CLit, CVar, CPlus, CAssign, CSequence, CWhile}.
--     Suspify :: Int
--       handles {CLit, CVar, CPlus, CAssign, CSequence, CWhile} where
--         Return x      -> return x
--         CLit x      k -> suspend undefined (do y <- cLit x;      k y)
--         CVar s      k -> suspend undefined (do y <- cVar s;      k y)
--         CPlus       k -> suspend undefined (do y <- cPlus;       k y)
--         CAssign s   k -> suspend undefined (do y <- cAssign s;   k y)
--         CSequence n k -> suspend undefined (do y <- cSequence n; k y)
--         CWhile      k -> suspend undefined (do y <- cWhile;      k y)
-- |]


[handler|
  forward h handles {Get (Env), Put (Env), Suspend h (Expr) (Int)}.
    Beval :: Int
      handles {CLit, CVar, CPlus, CAssign, CSequence, CWhile, Suspend (Beval h) (Expr) (Int)} where
        Return x         -> return x
        CLit x         k -> return x
        CVar s         k -> do e <- get
                               case lookup s e of
                                 Just x -> return x
                                 _      -> error "Variable not found!"
        CPlus          k -> do x <- k True
                               y <- k False
                               return (x + y)
        CAssign x      k -> do y <- k ()
                               e <- get
                               put ((x, y) : e)
                               return y
        CSequence n    k -> loop n
                            where
                              loop 0 = return 0
                              loop 1 = k 0
                              loop n = k (n-1) >> loop (n-1)
        CWhile         k -> loop
                            where
                              loop = do x <- k True
                                        if x == 0 then return 0
                                                  else k False >> loop
        Suspend e comp k -> do x <- suspend e (beval comp); k x
|]

[handler|
  forward h handles {Get (Env), Put (Env), ThrowError (String, String, Env), Suspend h (Expr) (Int)}.
    Eeval :: Int
      handles {CVar, Suspend (Eeval h) (Expr) (Int)} where
        Return x         -> return x
        CVar s         k -> do e <- get
                               case lookup s e of
                                 Just x -> return x
                                 _      -> throwError ("Variable not found!", s, e)
        Suspend e comp k -> do x <- suspend e (eeval comp); k x
|]

e1 = Plus (Lit 3) (Lit 4)
e2 = Plus (Assign "x" (Lit 3)) (Assign "y" (Lit 4))
e3 = Plus (Plus (Assign "x" (Lit 3)) (Assign "y" (Lit 4))) (Plus (Var "x") (Var "y"))
e4 = Plus (Plus (Assign "x" (Lit 3)) (Assign "y" (Lit 4))) (Plus (Var "x") (Var "z"))


test1 e = ioStringWriter (evalState [] (force (logger "eval" (beval (reflectSuspend e)))))
test2 e = ioStringWriter (evalState [] (force (dump (beval (reflectSuspend e)))))
test3 e = ioStringWriter (evalState [] (force (dump (logger "eval" (beval (reflectSuspend e))))))
test4 e = ioStringWriter (runError (evalState [] (force (beval (eeval (logger "eval" (reflectSuspend e)))))))
test5 e = ioStringWriter (runError (evalState [] (force (beval (eeval (dump (logger "eval" (reflectSuspend e))))))))
