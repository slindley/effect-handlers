{- n-queens with an without handlers -}

{-# LANGUAGE GADTs, TypeFamilies, RankNTypes,
    MultiParamTypeClasses, FlexibleInstances, OverlappingInstances,
    FlexibleContexts, UndecidableInstances, TypeOperators,
    QuasiQuotes
  #-}

import Criterion.Main

import Control.Monad
import Control.Applicative
import Data.Maybe

import Handlers
import TopLevel
import DesugarHandlers

[operation|forall a.Choose  :: [a] -> a|]

[handler|
  forward h.MaybeResults a :: Maybe a
    handles {Choose} where
      Return x    -> return (Just x)
      Choose xs k -> pickFirst xs
          where
            pickFirst []     = return Nothing
            pickFirst (x:xs) = do r <- k x
                                  case r of
                                    Just _  -> return r
                                    Nothing -> pickFirst xs
|]

-- contorted way of picking the first result or failing
-- without materialising a maybe type
[operation|forall a.Failure :: a|]

data Stack h a = Stack ([Stack h a -> Comp h a])
[handler|
  forward h handles {Failure}.FirstHandler a :: Stack h a -> a
    handles {Choose} where
      Return x        _              -> return x
      Choose []     k (Stack [])     -> failure
      Choose []     k (Stack (x:xs)) -> x (Stack xs)
      Choose (a:as) k (Stack l)      -> k a (Stack (map k as ++ l))
|]
firstResult comp = firstHandler (Stack []) comp

-- handle failure as undefined
[handler|
  UndefinedFailure a :: a handles {Failure} where
    Return x   -> x
    Failure  k -> undefined
|]

-- an alternative way of avoiding materialising a maybe type
[operation|Success a :: a -> ()|]
[handler|
  forward h handles {Success a}.SuccessFailure a :: () handles {Choose} where
    Return x    -> success x
    Choose xs k -> foldl (\c x -> c >> k x) (return ()) xs
|]
successOrFailure comp = successFailure comp

[handler|
  forward h.
    MaybeSuccess a :: Maybe a handles {Success a} where
      Return x    -> return Nothing
      Success v k -> return (Just v)
|]

failed :: [handles|h {Choose}|] => Comp h a
failed = choose []

safeAddition :: [Int] -> Int -> Int -> Bool
safeAddition [] _ _ = True
safeAddition (r:rows) row i =
   row /= r &&
   abs (row - r) /= i &&
   safeAddition rows row (i + 1)

-- hand-coded solution to the n-queens problem
queensPure :: Int -> [[Int]]
queensPure n = foldM f [] [1..n] where
    f rows _ = [row : rows |
                row <- [1..n],
                safeAddition rows row 1]

-- n queens using an abstract Choose operator
queensComp :: [handles|h {Choose}|] => Int -> Comp h [Int]
queensComp n = foldM f [] [1..n] where
    f rows _ = do row <- choose [1..n]
                  if (safeAddition rows row 1)
                    then return (row : rows)
                    else failed

--size = 22

pureTest    n = head (queensPure n)
maybeTest   n = fromJust (handlePure (maybeResults (queensComp n)))
successTest n = fromJust (handlePure (maybeSuccess (successFailure (queensComp n))))
firstTest   n = undefinedFailure (firstResult (queensComp n))

group n = bgroup "nqueens" [ bench "pure"     $ whnf pureTest    n
                           , bench "handlers" $ whnf maybeTest   n
                           , bench "success"  $ whnf successTest n
                           , bench "first"    $ whnf firstTest   n ]

main = do defaultMain [ group n | n <- [16..20] ]
