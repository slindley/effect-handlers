-- This example demonstrates that Oleg Kiselyov's iteratees are
-- algebraic computations and enumerators are effect handlers. It is a
-- transcription of the code from Section 3 of Oleg's FLOPS 2012
-- paper, Iteratees:
-- 
--   http://okmij.org/ftp/Haskell/Iteratee/describe.pdf

{-# LANGUAGE GADTs, TypeFamilies, NoMonomorphismRestriction, RankNTypes, ImpredicativeTypes,
    MultiParamTypeClasses, FlexibleInstances, OverlappingInstances,
    FlexibleContexts, TypeOperators, ScopedTypeVariables, BangPatterns #-}

import Control.Monad
import Control.Monad.State

import OpenHandlersCont

type LChar = Maybe Char

data GetC = GetC
type instance Return GetC = LChar
getC = doOp GetC

type I a = forall h.(h `Handles` GetC) => Comp h a

data EnStrHandler h a = EnStrHandler String
type instance Result (EnStrHandler h a) = Comp h a

instance (h `Handles` GetC) => (EnStrHandler h a `Handles` GetC) where
  clause GetC k (EnStrHandler "")    = do {c <- getC; k c (EnStrHandler "")}
  clause GetC k (EnStrHandler (c:t)) = k (Just c) (EnStrHandler t)

instance (h `Handles` op) => (EnStrHandler h a `Handles` op) where
    clause op k h = doOp op >>= (\x -> k x h)

en_str :: String -> I a -> I a
en_str s comp = handle comp (\x _ -> return x) (EnStrHandler s)

data PureRunHandler a = PureRunHandler
type instance Result (PureRunHandler a) = a

instance (PureRunHandler a `Handles` GetC) where
  clause GetC k h = k Nothing h
  
pureRun :: I a -> a
pureRun comp = handle comp (\x _ -> x) PureRunHandler

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

main = putStrLn (show $ countH 'a' (test 100000000))
