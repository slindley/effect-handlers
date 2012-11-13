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

type LChar = Maybe Char

count :: Char -> String -> Int
count c s = evalState (count' 0) s
  where
    count' :: Int -> State String Int
    count' !n = 
      do 
        s <- get
        case s of
          [] -> return n
          (c':cs) -> do {put cs; count' (if c==c' then (n+1) else n)}
        
test n = if n == 0 then ""
         else "abc" ++ test (n-1)

main = putStrLn (show $ count 'a' (test 100000000))
