{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction, RankNTypes,
    MultiParamTypeClasses,
    FlexibleContexts, TypeOperators, ScopedTypeVariables #-}

import Control.Monad
import OpenHandlers
import System.Random
import System.IO.Unsafe

import qualified Data.Map.Strict as Map

randDouble :: () -> Double
randDouble () = unsafePerformIO (getStdRandom random)

newtype Dist a = Dist [(Prob, a)]
type instance Return (Dist a) = a
dist ps = polyDoOp (Dist ps)

-- newtype Dice = Dice [Prob]
-- type instance Return Dice = Int
-- dice ps = doOp (Dice ps)

data Void

data Failure = Failure
type instance Return Failure = Void
failure = doOp Failure >>= undefined

type Prob = Double

--type P a = (h `Handles` Dice, h `Handles` Failure) => Comp h a
type P a = forall h.(h `PolyHandles` Dist, h `Handles` Failure) => Comp h a

data VC a = V a | C (PV a)
type PV a = [(Prob, VC a)]

instance (Show a) => Show (VC a) where
  show (V a) = show a
  show (C a) = "?"
  

data PVHandler a = PVHandler
type instance Result (PVHandler a) = PV a

-- instance (PVHandler a `Handles` Dice) where
--   clause h (Dice ps) k = zipWith (\p i -> (p, C (k h i))) ps [0..]

instance (PVHandler a `PolyHandles` Dist) where
  polyClause h (Dist ps) k = map (\(p, v) -> (p, C (k h v))) ps

instance (PVHandler a `Handles` Failure) where
  clause h Failure k = []
  
reify :: P a -> PV a
reify comp = handle comp PVHandler (const (\x -> [(1, V x)]))

-- dist' :: [(Prob, a)] -> P' a
-- dist' [] = failure
-- dist' l =
--   do
--     i <- dice (map fst l)
--     return $ snd (l !! i)
    
toss :: Prob -> P Bool
toss p = dist [(p, True), (1-p, False)]

infixl 2 &&&
(&&&) = liftM2 (&&)

infixl 1 |||
(|||) = liftM2 (||)

grassModel :: P Bool
grassModel =
  do
    rain <- toss 0.3
    sprinkler <- toss 0.5
    grassIsWet <-
          toss 0.9 &&& return rain
      ||| toss 0.8 &&& return sprinkler
      ||| toss 0.1
    if grassIsWet then return rain else failure

explore :: Ord a => Maybe Int -> PV a -> PV a
explore maxdepth choices = Map.foldrWithKey (\k p l -> (p, V k):l) susp ans
  where
    loop p depth down choices (answers@(ans, susp)) =
      case choices of
        [] -> answers
        (pt, V v):rest ->
          loop p depth down rest (Map.insertWith (+) v (pt * p) ans, susp)
        (pt, C c):rest | down ->
          let down' =
                case maxdepth of
                  Just x  -> depth < x
                  Nothing -> True
          in
           loop p depth down rest (loop (pt * p) (depth+1) down' c answers)
        (pt, c):rest ->
          loop p depth down rest (ans, (pt * p, c):susp)
    (ans, susp) = loop 1.0 0 True choices (Map.empty, [])
    
reflect :: PV a -> P a
reflect choices =
  do
    vc <- dist choices
    case vc of
      V a -> return a
      C pv -> reflect pv

(/==) = liftM2 (/=)

tossesXor :: Int -> P Bool
tossesXor n = loop n
  where
    loop :: Int -> P Bool
    loop n = if n == 1 then toss 0.5
             else toss 0.5 /== loop (n-1)

tossesXor' :: Int -> P Bool
tossesXor' n = loop n
  where
    loop :: Int -> P Bool
    loop n = if n == 1 then toss 0.5
             else
               do
                 r <- reflect (explore Nothing (reify (loop (n-1))))
                 toss 0.5 /== return r
