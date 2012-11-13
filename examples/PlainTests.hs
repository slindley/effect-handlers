import Control.Monad.State

count :: Int -> Int
count n = if n == 0 then n
          else count (n-1)

countM :: State Int Int
countM =
  do {n <- get;
      if n == 0 then return n
      else do {put (n-1); countM}}

test1 = runState countM 10000000000
test2 = count 10000000000
main = print test1

-- test1: 8.0 seconds
-- test2: 8.0 seconds
