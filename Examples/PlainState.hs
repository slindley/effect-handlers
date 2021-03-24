module Examples.PlainState where

import Control.Monad.State

import Criterion.Main
--import Criterion.Config

countPure :: Int -> Int
countPure n = if n == 0 then n
              else countPure (n-1)

count :: State Int Int
count =
  do {n <- get;
      if n == 0 then return n
      else do {put (n-1); count}}

iterations = 1000000000

monadic = runState count
pure'   = countPure

main = defaultMain [
       bgroup "state" [ bench "monadic" $ whnf monadic iterations
                      , bench "pure"    $ whnf pure'   iterations ]]
