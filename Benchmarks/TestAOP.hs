import Criterion.Main

import qualified Examples.AOP as H
import qualified Benchmarks.MRI_code.Interpreters as M
import qualified Benchmarks.MonadicEval as P

import Benchmarks.MRI_code.Interpreters (Expr(..), Env)

import System.Random

randomLit :: IO Int
randomLit = getStdRandom (randomR(0, (2^16)-1))

randomBool :: IO Bool
randomBool = getStdRandom random

-- Generate a random expression tree of size n, consisting only of
-- Plus nodes and Lit leaves.
randomExpr :: Int -> IO Expr
randomExpr 1 = do n <- randomLit
                  return $ Lit n
randomExpr n = do i <- getStdRandom (randomR(1, n-1))
                  l <- randomExpr i
                  r <- randomExpr (n-i)
                  return $ Plus l r

makeGroup n =
  do e <- randomExpr n
     return $ bgroup (show n) [ bgroup "AOP" [ bench "concrete" $ whnf last (P.logdumptest e)
                                             , bench "mixins"   $ whnf last (M.test2 e)
                                             , bench "handlers" $ whnf last (H.logdumptest e) ] ]

seed = 42

main = do setStdGen (mkStdGen seed);
          gs <- sequence [makeGroup (2^n) | n <- [10..14]]
          defaultMain gs
