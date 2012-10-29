{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction, RankNTypes,
    MultiParamTypeClasses, FlexibleInstances, GADTs,
    OverlappingInstances, QuasiQuotes, TemplateHaskell,
    FlexibleContexts, TypeOperators, ScopedTypeVariables, ConstraintKinds #-}

import Control.Monad
import System.Random
import System.IO.Unsafe
import Unsafe.Coerce

import qualified Data.Map.Strict as Map

import OpenHandlers
import DesugarHandlers

--randDouble :: () -> Double
--randDouble () = unsafePerformIO (getStdRandom random)

mass :: [(Prob, a)] -> Double
mass = sum . (map fst)

normalise :: [(Prob, a)] -> [(Prob, a)]
normalise ps = map (\ (p, v) -> (p / m, v) ) ps
  where
    m = mass ps

[operation|forall a.Dist    : [(Prob, a)] -> a|]
[operation|forall a.Failure : a|] 

type Prob = Double

type DistFail h = (h `PolyHandles` Dist, h `PolyHandles` Failure)
type LazyForce h = (h `PolyHandles` LetLazy, h `PolyHandles` Force)

-- type P a = forall h.(DistFail h, LazyForce h) => Comp h a
-- type Q a = forall h.DistFail h => Comp h a

type P a = forall h.(h `PolyHandles` LetLazy, h `PolyHandles` Force,
                     h `PolyHandles` Dist, h `PolyHandles` Failure) => Comp h a
type Q a = forall h.(h `PolyHandles` Dist, h `PolyHandles` Failure) => Comp h a

data VC a = V a | C (PV a)
--  deriving Show
type PV a = [(Prob, VC a)]

instance (Show a) => Show (VC a) where
  show (V a) = show a
  show (C a) = "?"

[handler|PVHandler a : PV a handles {Dist, Failure} where
  polyClause h (Dist ps) k = map (\(p, v) -> (p, C (k h v))) ps
  polyClause h Failure   k = []
|]


--data PVHandler h a = PVHandler
--type instance Result (PVHandler h a) = Comp h (PV a)

-- instance (PVHandler h a `PolyHandles` Dist) where
--   polyClause h (Dist ps) k = mapM (\(p, v) -> do {t <- k h v; return $ (p, C t)}) ps
-- instance (PVHandler h a `PolyHandles` Failure) where
--   polyClause h Failure k = return []

-- instance (h `Handles` op) => (PVHandler h a `Handles` op) where
--   clause h op k = doOp op >>= k h
-- instance (h `PolyHandles` op) => (PVHandler h a `PolyHandles` op) where
--   polyClause h op k = polyDoOp op >>= k h

reify0 :: Q a -> PV a
reify0 comp =
  handle comp PVHandler (const (\x -> [(1, V x)]))

reify :: P a -> PV a
reify comp =
  handle (handle comp letLazyHandler (const return)) PVHandler (const (\x -> [(1, V x)]))

-- dist' :: [(Prob, a)] -> P' a
-- dist' [] = failure
-- dist' l =
--   do
--     i <- dice (map fst l)
--     return $ snd (l !! i)
    
toss :: Prob -> Q Bool
toss p = dist [(p, True), (1-p, False)]

-- In a monadic setting we must make boolean short circuit evaluation
-- explicit
infixl 2 &&&
p &&& q = do {x <- p; if x then q else return False}

infixl 1 |||
p ||| q = do {x <- p; if x then return True else q}

grassModel :: Q Bool
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
    
reflect :: PV a -> Q a
reflect choices =
  do
    vc <- dist choices
    case vc of
      V a -> return a
      C pv -> reflect pv
      
reflectUntil :: Int -> PV a -> Q' a
reflectUntil n choices =
  do
    choice <- dist choices
    case choice of
      V a        -> return a
      C choices' -> if n == 0 then stop choice
                    else reflectUntil (n-1) choices'
      
[operation|forall r.Stop a : VC a -> r|]

--type Q' a = forall h.(DistFail h, h `PolyHandles` Stop a) => Comp h a
type Q' a = forall h.(h `PolyHandles` Dist, h `PolyHandles` Failure, h `PolyHandles` Stop a) => Comp h a


[handler|
  forward h.ExploreHandler a : Prob -> Map.Map a Prob -> Comp h (Map.Map a Prob)
    handles {Failure, Dist} where
      polyClause (ExploreHandler _ m) Failure      k = return m
      polyClause (ExploreHandler s m) (Dist ps)    k =
        foldM (\m' (p, v) -> k (ExploreHandler (s*p) m') v) m ps
|]
    
-- data ExploreHandler h a = ExploreHandler Prob (Map.Map a Prob)
-- type instance Result (ExploreHandler h a) = Map.Map a Prob

-- instance ExploreHandler h a `PolyHandles` Failure where
--   polyClause (ExploreHandler _ m) Failure k = m
-- instance ExploreHandler h a `PolyHandles` Dist where
--   polyClause (ExploreHandler s m) (Dist ps) k = foldl (\m' (p, v) -> k (ExploreHandler (s*p) m') v) m ps

exploreHandler :: Ord a => Comp (ExploreHandler h a) a -> Comp h [(Prob, a)]
exploreHandler comp =
  ans >>= return . (Map.foldrWithKey (\k p l -> (p, k):l) [])
  where
    ans =
      handle comp (ExploreHandler 1 Map.empty)
      (\(ExploreHandler s m) x ->
        return 
        (case Map.lookup x m of
          Nothing -> Map.insert x s m
          Just p  -> Map.insert x (s+p) m))


[handler|
  ExploreUntilHandler a : Prob -> Map.Map a Prob -> PV a -> (Map.Map a Prob, PV a)
    handles {Failure, Dist, Stop a} where
      polyClause (ExploreUntilHandler _ m susp) Failure   k = (m, susp)
      polyClause (ExploreUntilHandler s m susp) (Dist ps) k =
        foldl
          (\(m', susp') (p, v) ->
            k (ExploreUntilHandler (s*p) m' susp') v)
          (m, susp)
          ps
      polyClause (ExploreUntilHandler s m susp) (Stop c)  k = (m, (s, c) : susp)
|]

explore' (Just i) comp = exploreUntilHandler (reflectUntil (i+1) comp)
explore' Nothing  comp = exploreUntilHandler (reflect comp)

exploreUntilHandler :: Ord a => Q' a -> PV a
exploreUntilHandler comp =
  Map.foldrWithKey (\k p l -> (p, V k):l) susp ans
  where
    (ans, susp) =
      handle comp (ExploreUntilHandler 1 Map.empty [])
      (\(ExploreUntilHandler s m susp) x ->
        (Map.insertWith (+) x s m, susp))


(/==) = liftM2 (/=)

tossesXor :: Int -> Q Bool
tossesXor n = loop n
  where
    loop :: Int -> Q Bool
    loop n = if n == 1 then toss 0.5
             else toss 0.5 /== loop (n-1)

tossesXor' :: Int -> Q Bool
tossesXor' n = loop n
  where
    loop :: Int -> Q Bool
    loop n = if n == 1 then toss 0.5
             else
               do
                 r <- reflect (explore Nothing (reify (loop (n-1))))
                 toss 0.5 /== return r


newtype LazyVar a = LazyVar Int

letLazy :: (h `PolyHandles` LetLazy) => Q a -> Comp h (LazyVar a)
[operation|forall a.LetLazy : Q a -> LazyVar a|]
[operation|forall a.Force   : LazyVar a -> a|]

-- newtype BoxQ a = BoxQ {unBoxQ :: Q a}

data EitherComp where
  LeftComp :: Q a -> EitherComp
  RightComp :: a -> EitherComp


type CompMap = Map.Map Int EitherComp

forceComp :: Int -> CompMap -> Q (a, CompMap)
forceComp x m =
  case Map.lookup x m of
    Just (LeftComp q)  ->
      do
        v <- q
        let m' = Map.insert x (RightComp v) m     
        return (unsafeCoerce v, m')
    Just (RightComp v) -> return (unsafeCoerce v, m)

[handler|
  forward h.(h `PolyHandles` Dist, h `PolyHandles` Failure) =>
    LetLazyHandler a : Int -> CompMap -> Comp h a handles {LetLazy, Force} where
      polyClause (LetLazyHandler x m) (LetLazy q) k =
        k (LetLazyHandler (x+1) (Map.insert x (LeftComp q) m)) (LazyVar x)
      polyClause (LetLazyHandler y m) (Force (LazyVar x)) k =
        do {(v, m') <- forceComp x m; k (LetLazyHandler y m') v}
|]
-- we need to give the Force clause as an explicit type class
-- instance, as it includes additional type class constraints
-- instance (h `PolyHandles` Dist, h `PolyHandles` Failure) => (LetLazyHandler h a `PolyHandles` Force) where
--   polyClause (LetLazyHandler y m) (Force (LazyVar x)) k =
--     do {(v, m') <- forceComp x m; k (LetLazyHandler y m') v}

-- data LetLazyHandler h a = LetLazyHandler Int CompMap
-- type instance Result (LetLazyHandler h a) = Comp h a

-- instance (LetLazyHandler h a `PolyHandles` LetLazy) where
--   polyClause (LetLazyHandler x m) (LetLazy q) k =
--     k (LetLazyHandler (x+1) (Map.insert x (LeftComp q) m)) (LazyVar x)

-- instance (h `Handles` op) => (LetLazyHandler h a `Handles` op) where
--   clause h op k = doOp op >>= k h
-- instance (h `PolyHandles` op) => (LetLazyHandler h a `PolyHandles` op) where
--   polyClause h op k = polyDoOp op >>= k h

letLazyHandler :: LetLazyHandler h a
letLazyHandler = LetLazyHandler 0 Map.empty

tosses' :: Int -> Q [Bool]
tosses' 0 = return []
tosses' n =
  do
    v <- toss 0.5
    vs <- tosses' (n-1)
    return (v : vs)
    
allHeads' :: Int -> Q Bool
allHeads' n =
  do
    l <- tosses' n
    return (all id l)

tosses :: Int -> P [LazyVar Bool]
tosses 0 = return []
tosses n =
  do
    v <- letLazy (toss 0.5)
    vs <- tosses (n-1)
    return (v : vs)
    
allHeads :: Int -> P Bool
allHeads n =
  do
    vs <- tosses n
    loop vs
    where
      loop []     = return True
      loop (v:vs) =
        do
          v' <- force v
          if v' then loop vs else return False

[operation|Rand : Double|]

[handler|forward h.(h `Handles` Rand) => SampleHandler a : Comp h a handles {Dist} where
  polyClause h (Dist ps) k =
    do
      r <- rand
      let target = r * mass ps          
      k h (accum 0 target ps)
      where
        accum :: forall b.Double -> Double -> [(Prob, b)] -> b
        accum x target []                          = undefined 
        accum x target ((y, v):l) | (x+y) > target = v
        accum x target ((y, v):l)                  = accum (x+y) target l
|]

-- data SampleHandler h a = SampleHandler
-- type instance  Result (SampleHandler h a) = Comp h a

-- explicit class constraints
-- instance (h `Handles` Rand) => (SampleHandler h a `PolyHandles` Dist) where
--   polyClause h (Dist ps) k =
--     do
--       r <- rand
--       let target = r * mass ps          
--       k h (accum 0 target ps)
--       where
--         accum :: Double -> Double -> [(Prob, b)] -> b
--         accum x target []                          = undefined 
--         accum x target ((y, v):l) | (x+y) > target = v
--         accum x target ((y, v):l)                  = accum (x+y) target l

[handler|
  forward h.(h `Handles` Rand) =>
    ImportanceHandler a : Int -> Double -> Comp h ([(Prob, a)])
      handles {Failure} where
        polyClause h Failure k = return []    
|]

-- instance (h `Handles` Rand) => ImportanceHandler h a `PolyHandles` Failure where
--   polyClause h Failure k = return []    
  
-- -- explicit class constraints
-- instance (h `Handles` Rand) => ImportanceHandler h a `PolyHandles` Dist where
--   polyClause h (Dist ps) k =
--     do
--       r <- rand
--       let target = r * mass ps          
--       k h (accum 0 target ps)
--       where
--         accum :: Double -> Double -> [(Prob, b)] -> b
--         accum x target []                          = undefined 
--         accum x target ((y, v):l) | (x+y) > target = v
--         accum x target ((y, v):l)                  = accum (x+y) target l


-- instance (h `Handles` op) => (SampleHandler h a `Handles` op) where
--   clause h op k = doOp op >>= k h
-- instance (h `PolyHandles` op) => (SampleHandler h a `PolyHandles` op) where
--   polyClause h op k = polyDoOp op >>= k h


importanceSample :: (Ord a, h `Handles` Rand, h `PolyHandles` Dist) => Int -> Q a -> Comp h a
importanceSample i comp = do {ps <- importance 1.0 (reify0 comp); dist ps}
  where
    importance :: (Ord a, h `Handles` Rand) => Double -> PV a -> Comp h ([(Prob, a)])
    importance s pv' =
      case cs of
        [] -> return vs
        _  -> 
          do
            r <- rand
            let target = r * csum
            return (vs ++) `ap` importance s' (accum 0 target cs)
      where
        accum :: Double -> Double -> [(Prob, PV b)] -> PV b
        accum x target []                          = undefined 
        accum x target ((y, v):l) | (x+y) > target = v
        accum x target ((y, v):l)                  = accum (x+y) target l

        pv = explore (Just i) pv'
        vs' = [(p, v) | (p, V v) <- pv]
        cs =  [(p, c) | (p, C c) <- pv]
        vsum = sum (map fst vs')
        csum = sum (map fst cs)
        vcsum = vsum + csum
        factor = s / vcsum
        s' = csum * factor
        vs = [(p * factor, v) | (p, v) <- vs']
    
[handler|
  forward h.SampleLoop a : Comp (SampleLoop h a) a -> Comp h a handles {Failure} where
    polyClause h@(SampleLoop comp) Failure k = handle comp h (const return)
|]

sample :: Comp (SampleHandler h a) a -> Comp h a
sample comp = handle comp SampleHandler (const return)

sampleLoop :: Q a -> IO a
sampleLoop comp = handleIO (handle (sample comp) (SampleLoop (sample comp)) (const return))
    
instance IOHandler a `Handles` Rand where
  clause h Rand k =
    do
      r <- getStdRandom random
      k h r

samples :: Ord a => Q a -> Int -> IO [(Prob, a)]
samples comp n =
  handleIO (exploreHandler
                    (do
                        let l = take n (repeat (1, ()))
                        () <- dist l
                        sample comp))


importanceSamples :: Ord a => Int -> Q a -> Int -> IO [(Prob, a)]
importanceSamples i comp n =
  handleIO (exploreHandler
                    (do
                        let l = take n (repeat (1, ()))
                        () <- dist l
                        importanceSample i comp))


drunkCoin :: Q Bool
drunkCoin =
  do
    t <- toss 0.5
    lost <- toss 0.9
    if lost then failure else return t
    
dcoinAnd :: Int -> Q Bool
dcoinAnd 1 = drunkCoin
dcoinAnd n =  drunkCoin &&& dcoinAnd (n-1)
