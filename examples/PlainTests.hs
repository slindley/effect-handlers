import Control.Monad.State

import Criterion.Main
import Criterion.Config

countPure :: Int -> Int
countPure n = if n == 0 then n
              else countPure (n-1)

count :: State Int Int
count =
  do {n <- get;
      if n == 0 then return n
      else do {put (n-1); count}}

-- test1 = runState count 10000000000
-- test2 = countPure 10000000000
-- main = print test1

config = defaultConfig {
               cfgSamples = ljust 10
            }

main = defaultMainWith config (return ()) [
       bgroup "state" [ bench "monadic" $ whnf (runState count) 1000000000
                      , bench "pure"    $ whnf (countPure)      1000000000 ]]


-- test1: 8.0 seconds
-- test2: 8.0 seconds
