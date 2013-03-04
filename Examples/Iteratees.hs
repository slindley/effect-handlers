-- This example demonstrates that Oleg Kiselyov's iteratees are
-- algebraic computations and enumerators are effect handlers. It is a
-- transcription of the code from Section 3 of Oleg's FLOPS 2012
-- paper, Iteratees:
-- 
--   http://okmij.org/ftp/Haskell/Iteratee/describe.pdf

{-# LANGUAGE GADTs, TypeFamilies, NoMonomorphismRestriction, RankNTypes, ImpredicativeTypes,
    MultiParamTypeClasses, FlexibleInstances, OverlappingInstances, UndecidableInstances,
    FlexibleContexts, TypeOperators, ScopedTypeVariables, BangPatterns, 
    QuasiQuotes
 #-}

import Control.Monad

import Handlers
import DesugarHandlers

type LChar = Maybe Char

[operation|GetC :: LChar|]
-- data GetC (s :: *) (t :: *) where
--   GetC :: GetC () ()
-- type instance Return (GetC () ()) = LChar
-- getC :: ((h `Handles` GetC) ()) => Comp h LChar
-- getC = doOp GetC

type I a = forall h.[handles|h {GetC}|] => Comp h a

getline :: I String
getline = loop ""
  where loop acc =
          do w <- getC
             check acc w
        check acc (Just c) | c /= '\n' = loop (c:acc)
        check acc _                    = return (reverse acc)

[handler|
  EvalHandler a :: String -> a handles {GetC} where
    GetC     k ""    -> k Nothing ""
    GetC     k (c:t) -> k (Just c) t
    Return x   _     -> x
|]

eval :: String -> I a -> a
eval s comp = evalHandler s comp

getlines :: I [String]
getlines = loop []
  where loop acc = getline >>= check acc
        check acc "" = return (reverse acc)
        check acc l  = loop (l:acc)


[handler|
  forward h handles {GetC}.EnStrHandler a :: String -> a
    handles {GetC} where
      Return x   _     -> return x
      GetC     k ""    -> do {c <- getC; k c ""}
      GetC     k (c:t) -> k (Just c) t
|]

-- data EnStrHandler (h :: *) (a :: *) = EnStrHandler String
-- type instance Result (EnStrHandler h a) = Comp h a

-- instance ((h `Handles` GetC) ()) => ((EnStrHandler h a `Handles` GetC) ()) where
--   clause GetC k (EnStrHandler "")    = do {c <- getC; k c (EnStrHandler "")}
--   clause GetC k (EnStrHandler (c:t)) = k (Just c) (EnStrHandler t)

-- instance ((h `Handles` op) args) => ((EnStrHandler h a `Handles` op) args) where
--     clause op k h = doOp op >>= (\x -> k x h)

en_str :: String -> I a -> I a
en_str s comp = enStrHandler s comp


-- RunHandler throws away any outstanding unhandled GetC applications
[handler|
  forward h.RunHandler a :: a handles {GetC} where
    GetC     k -> k Nothing
    Return x   -> return x
|]

run :: I a -> Comp h a
run comp = runHandler comp


-- like RunHandler but with no underlying handler
[handler|
  PureRun a :: a handles {GetC} where
    GetC   k -> k Nothing
    Return x -> x
|]

-- data PureRunHandler (a :: *) = PureRunHandler
-- type instance Result (PureRunHandler a) = a
-- instance ((PureRunHandler a `Handles` GetC) ()) where
--   clause GetC k h = k Nothing h
-- pureRun :: I a -> a
-- pureRun comp = handle comp (\x _ -> x) PureRunHandler



data FlipState h a = FlipState Bool LChar (LChar -> FlipState h a -> Comp h a)
[handler|
  forward h handles {GetC}.
    FlipHandler a :: FlipState h a -> a handles {GetC} where
      GetC     kl (FlipState True  c kr) -> do {kr c (FlipState False c kl)}
      GetC     kr (FlipState False _ kl) -> do {c <- getC; kl c (FlipState True c kr)}
      Return x    _                      -> return x
|]


-- synchronise two iteratees
(<|) :: I a -> I a -> I a
l <| r = flipHandler (FlipState True Nothing (\Nothing s -> flipHandler s r)) l


-- Roughly, we get the following behaviour from the synchronised
-- traces of (l <| r):
-- 
--     ls1...GetC...ls2...GetC...  ...GetC...lsn
--            ||           ||          ||
--     rs1...GetC...rs2...GetC...  ...GetC...rsn
--
-- becomes:
--
--     ls1,rs1, GetC, ls2,rs2, GetC,...,GetC lsn,rsn

-- fetch characters forever
failure :: I a
failure = getC >>= const failure

empty :: a -> I a
empty = return

oneL :: I LChar
oneL = getC

one :: I Char
one = oneL >>= maybe failure return

pSat :: (LChar -> Bool) -> I LChar
pSat pred = oneL >>= \c -> if pred c then return c else failure

pGetline :: I String
pGetline = nl <| liftM2 (:) one pGetline
  where nl =
          do
            pSat (\c -> c == Just '\n' || c == Nothing)
            return ""
            
pGetline' :: I String
pGetline' = oneL >>= check
  where check (Just '\n') = return ""
        check Nothing     = return ""
        check (Just c)    = liftM (c:) pGetline'



countI :: Char -> I Int
countI c = count' 0
  where
    count' :: Int -> I Int
    count' !n =
      do
        mc <- getC
        case mc of
            Nothing -> return n
            Just c' -> count' (if c==c' then n+1 else n)
         
countH :: Char -> String -> Int
countH c s = pureRun (en_str s (countI c))
       
test n = if n == 0 then ""
         else "abc" ++ test (n-1)

main = print (countH 'a' (test 100000000))

-- test 100000000 results:
--   oleg: 13.4
--   continuation monad: 9.7
--   codensity: 13.9
--   free monad: 17.3

-- -- count :: Char -> String -> Int
-- -- count c s = evalState (count' 0) s
-- --   where
-- --     count' :: Int -> State String Int
-- --     count' !n = 
-- --       do 
-- --         s <- get
-- --         case s of
-- --           [] -> return n
-- --           (c':cs) -> do {put cs; count' (if c==c' then (n+1) else n)}
        
-- -- test n = if n == 0 then ""
-- --          else "abc" ++ test (n-1)

