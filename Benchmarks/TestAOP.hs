import Criterion.Main
import Criterion.Config

import Examples.AOP
import System.Random

randomLit :: IO Int
randomLit = getStdRandom (randomR(0, 1023))

randomBool :: IO Bool
randomBool = getStdRandom random

-- Generate a random expression tree of size n, consisting only of
-- Plus nodes and Lit leaves.
randomExp :: Int -> IO Expr
randomExp 1 = do n <- randomLit
                 return $ Lit n
randomExp n = do i <- getStdRandom (randomR(1, n-1))
                 l <- randomExp i
                 r <- randomExp (n-i)
                 return $ Plus l r
