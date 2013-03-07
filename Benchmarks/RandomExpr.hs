import Examples.AOP
import System.Random

randomLit :: IO Int
randomLit = getStdRandom (randomR(0, 1023))

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
