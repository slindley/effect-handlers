-- This example demonstrates that Oleg Kiselyov's iteratees are
-- algebraic computations and enumerators are effect handlers. It is a
-- transcription of the code from Section 3 of Oleg's FLOPS 2012
-- paper, Iteratees:
-- 
--   http://okmij.org/ftp/Haskell/Iteratee/describe.pdf

{-# LANGUAGE GADTs, TypeFamilies, NoMonomorphismRestriction, RankNTypes,
    MultiParamTypeClasses, FlexibleInstances, OverlappingInstances,
    FlexibleContexts, TypeOperators, ScopedTypeVariables, BangPatterns #-}

import Control.Monad
import OpenHandlers

type LChar = Maybe Char

data GetC = GetC
type instance Return GetC = LChar
getC = doOp GetC

type I a = forall h.(h `Handles` GetC) => Comp h a

getline :: I String
getline = loop ""
  where loop acc =
          do w <- getC
             check acc w
        check acc (Just c) | c /= '\n' = loop (c:acc)
        check acc _                    = return (reverse acc)

data EvalHandler a = EvalHandler String
type instance Result (EvalHandler a) = a

instance (EvalHandler a `Handles` GetC) where
  clause (EvalHandler "")    GetC k = k (EvalHandler "") Nothing
  clause (EvalHandler (c:t)) GetC k = k (EvalHandler t) (Just c)

eval :: String -> I a -> a
eval s comp =
    handle comp (EvalHandler s) (const id)

getlines :: I [String]
getlines = loop []
  where loop acc = getline >>= check acc
        check acc "" = return (reverse acc)
        check acc l  = loop (l:acc)
        
data EnStrHandler h a = EnStrHandler String
type instance Result (EnStrHandler h a) = Comp h a

instance (h `Handles` GetC) => (EnStrHandler h a `Handles` GetC) where
  clause (EnStrHandler "")    GetC k = do {c <- getC; k (EnStrHandler "") c}
  clause (EnStrHandler (c:t)) GetC k = k (EnStrHandler t) (Just c)

instance (h `Handles` op) => (EnStrHandler h a `Handles` op) where
    clause h op k = doOp op >>= k h

en_str :: String -> I a -> I a
en_str s comp = handle comp (EnStrHandler s) (const return)

-- RunHandler throws away any outstanding unhandled GetC applications
data RunHandler h a = RunHandler
type instance Result (RunHandler h a) = Comp h a

instance (RunHandler h a `Handles` GetC) where
  clause h GetC k = k h Nothing

instance (h `Handles` op) => (RunHandler h a `Handles` op) where
  clause h op k = doOp op >>= k h

run :: I a -> Comp h a
run comp = handle comp RunHandler (const return)

-- like PureRunHandler but with no underlying handler
data PureRunHandler a = PureRunHandler
type instance Result (PureRunHandler a) = a

instance (PureRunHandler a `Handles` GetC) where
  clause h GetC k = k h Nothing
  
pureRun :: I a -> a
pureRun comp = handle comp PureRunHandler (const id)

data FlipHandler h a = (h `Handles` GetC) => FlipHandler (Bool, LChar, FlipHandler h a -> LChar -> Comp h a)
type instance Result (FlipHandler h a) = Comp h a

instance (FlipHandler h a `Handles` GetC) where
  clause (FlipHandler (True,  c, kr)) GetC kl = do {kr (FlipHandler (False, c, kl)) c}
  clause (FlipHandler (False, _, kl)) GetC kr = do {c <- getC; kl (FlipHandler (True, c, kr)) c}

instance (h `Handles` op) => (FlipHandler h a `Handles` op) where
  clause h op k = doOp op >>= k h

-- synchronise two iteratees
(<|) :: I a -> I a -> I a
l <| r = handle l (FlipHandler (True, Nothing, \h' Nothing -> handle r h' (const return))) (const return)

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

count :: Char -> String -> Int
count c s = count' s 0
  where
    count' :: String -> Int -> Int
    count' []      !n = n
    count' (c':cs) !n = count' cs (if c==c' then n+1 else n)
    
test n = if n == 0 then ""
         else "abc" ++ test (n-1)

main = putStrLn (show $ countH 'a' (test 100000000))
