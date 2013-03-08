{-
  Oleg's original implementation of iteratees. 

  This example demonstrates that Oleg Kiselyov's iteratees are
  algebraic computations and enumerators are effect handlers. It is a
  transcription of the code from Section 3 of Oleg's FLOPS 2012
  paper, Iteratees:

    http://okmij.org/ftp/Haskell/Iteratee/describe.pdf
-}
{-# LANGUAGE BangPatterns #-}

import Control.Monad

type LChar = Maybe Char

data I a = Done a
         | GetC (LChar -> I a)

getC = GetC return

instance Monad I where
  return = Done
  
  Done x >>= f = f x
  GetC k >>= f = GetC (k >=> f)

getline :: I String
getline = loop ""
  where loop acc =
          do w <- getC
             check acc w
        check acc (Just c) | c /= '\n' = loop (c:acc)
        check acc _                    = return (reverse acc)

eval :: String -> I a -> a
eval ""    (GetC k) = eval "" $ k Nothing
eval (c:t) (GetC k) = eval t  $ k (Just c)
eval str   (Done x) = x

getlines :: I [String]
getlines = loop []
  where loop acc = getline >>= check acc
        check acc "" = return (reverse acc)
        check acc l  = loop (l:acc)
        

en_str :: String -> I a -> I a
en_str ""    i        = i
en_str (c:t) (GetC k) = en_str t $ k (Just c)
en_str _     (Done x) = return x

run :: I a -> a
run (GetC k) = run $ k Nothing
run (Done x) = x

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
countH c s = run (en_str s (countI c))

count :: Char -> String -> Int
count c s = count' s 0
  where
    count' :: String -> Int -> Int
    count' []      !n = n
    count' (c':cs) !n = count' cs (if c==c' then n+1 else n)
    
test n = if n == 0 then ""
         else "abc" ++ test (n-1)

main = print $ countH 'a' (test 100000000)
