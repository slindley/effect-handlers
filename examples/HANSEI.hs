{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction, RankNTypes,
    MultiParamTypeClasses, FlexibleInstances, GADTs,
    OverlappingInstances, QuasiQuotes, TemplateHaskell,
    FlexibleContexts, TypeOperators, ScopedTypeVariables, ConstraintKinds #-}

import Control.Monad
import System.Random
import Unsafe.Coerce

import qualified Data.Map.Strict as Map

import Handlers
import DesugarHandlers

mass :: [(Prob, a)] -> Double
mass = sum . (map fst)

normalise :: [(Prob, a)] -> [(Prob, a)]
normalise ps = map (\ (p, v) -> (p / m, v) ) ps
  where
    m = mass ps

undup :: Ord a => [(Prob, a)] -> [(Prob, a)]
undup ps = Map.foldrWithKey (\k p l -> (p, k):l) [] m
  where
    m = foldl (\m (p, v) -> Map.insertWith (+) v p m) Map.empty ps
  
scale :: Double -> [(Prob, a)] -> [(Prob, a)]
scale s = map (\(p, v) -> (s*p, v))

accum :: Double -> Double -> [(Prob, a)] -> a
accum x target []                          = undefined 
accum x target ((y, v):l) | (x+y) > target = v
accum x target ((y, v):l)                  = accum (x+y) target l

[operation|forall a.Dist    :: [(Prob, a)] -> a|]
[operation|forall a.Failure :: a|] 

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
  show (C a) = ".."

[handler|PVHandler a :: PV a polyhandles {Dist, Failure} where
  Dist ps  k -> map (\(p, v) -> (p, C (k v))) ps
  Failure  k -> []
  Return x   -> [(1, V x)]
|]

reify0 :: Q a -> PV a
reify0 comp = pVHandler comp

reify :: P a -> PV a
reify comp = pVHandler (letLazyHandler' comp)

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
reflect [] = failure
reflect choices =
  do
    vc <- dist choices
    case vc of
      V a -> return a
      C pv -> reflect pv
   
reflectUntil :: Int -> PV a -> Q' a
reflectUntil _ [] = failure
reflectUntil n choices =
  do
    choice <- dist choices
    case choice of
      V a        -> return a
      C choices' -> if n == 0 then stop choice
                    else reflectUntil (n-1) choices'
   
[operation|forall r.Stop a :: VC a -> r|]

--type Q' a = forall h.(DistFail h, h `PolyHandles` Stop a) => Comp h a
type Q' a = forall h.(h `PolyHandles` Dist, h `PolyHandles` Failure, h `PolyHandles` Stop a) => Comp h a

[handler|
  forward h.ExploreHandler a :: Prob -> Map.Map a Prob -> Map.Map a Prob
    polyhandles {Failure, Dist} where
      Failure  k _ m -> return m
      Dist ps  k s m -> foldM (\m' (p, v) -> k v (s*p) m') m ps
      Return x   s m ->
        return 
        (case Map.lookup x m of
          Nothing -> Map.insert x s m
          Just p  -> Map.insert x (s+p) m)
|]
  
exploreHandler' :: Ord a => Comp (ExploreHandler h a) a -> Comp h [(Prob, a)]
exploreHandler' comp =
  exploreHandler 1 Map.empty comp >>= return . (Map.foldrWithKey (\k p l -> (p, k):l) [])

[handler|
  ExploreUntilHandler a :: Prob -> Map.Map a Prob -> PV a -> (Map.Map a Prob, PV a)
    polyhandles {Failure, Dist, Stop a} where
      Failure   k _ m susp -> (m, susp)
      Dist ps   k s m susp ->
        foldl
          (\(m', susp') (p, v) ->
            k v (s*p) m' susp')
          (m, susp)
          ps
      Stop c    k s m susp -> (m, (s, c) : susp)
      Return x    s m susp ->
        (Map.insertWith (+) x s m, susp)
|]

explore' :: Ord a => Maybe Int -> PV a -> PV a
explore' (Just i) comp = exploreUntilHandler' (reflectUntil (i+1) comp)
explore' Nothing  comp = exploreUntilHandler' (reflect comp)

exploreUntilHandler' :: Ord a => Q' a -> PV a
exploreUntilHandler' comp =
  Map.foldrWithKey (\k p l -> (p, V k):l) susp ans
  where
    (ans, susp) = exploreUntilHandler 1 Map.empty [] comp

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

--letLazy :: (h `PolyHandles` LetLazy) => Q a -> Comp h (LazyVar a)
[operation|forall a.LetLazy :: Q a -> LazyVar a|]
[operation|forall a.Force   :: LazyVar a -> a|]

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
    LetLazyHandler a :: Int -> CompMap -> a
      polyhandles {LetLazy, Force} where
        LetLazy q         k x m ->
          k (LazyVar x) (x+1) (Map.insert x (LeftComp q) m)
        Force (LazyVar x) k y m ->
          do {(v, m') <- forceComp x m; k v y m'}
        Return x            _ _ -> return x
|]

letLazyHandler' :: P a -> Q a
letLazyHandler' comp = letLazyHandler 0 Map.empty comp

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

[operation|Rand :: Double|]

[handler|
  forward h.(h `Handles` Rand) => SampleHandler a :: a
    polyhandles {Dist} where
      Dist ps  k ->
        do
          r <- rand
          let target = r * mass ps
          k (accum 0 target ps)
      Return x   -> return x
|]


-- what's this for?
[handler|
  forward h.(h `Handles` Rand) =>
    ImportanceHandler a :: Int -> Double -> [(Prob, a)]
      polyhandles {Dist,Failure} where
        Dist ps k n s ->
          do
            r <- rand
            let target = r * mass ps          
            k (accum 0 target ps) n s
        Failure k _ _ -> return []    
        Return x  _ _ -> return [(1, x)]
|]


importanceSample :: (Ord a, h `Handles` Rand, h `PolyHandles` Dist) => Int -> Q a -> Comp h a
importanceSample i comp =
  do 
    ps <- importance 1.0 (reify0 comp)
    dist ps
    where
      importance :: (Ord a, h `Handles` Rand) => Double -> PV a -> Comp h ([(Prob, a)])
      importance s pv' =
        case cs of
          [] -> return vs
          _  -> 
            do
              r <- rand
              let target = r * csum
              fmap (vs ++) (importance (s*csum) (accum 0 target cs))
        where
          pv = explore' (Just i) pv'
          vs  = [(s*p, v) | (p, V v) <- pv]
          cs  = [(p, c) | (p, C c)  <- pv, length c /= 0]
          csum = sum (map fst cs)

importance' :: (Ord a) => Int -> Double -> PV a -> IO ([(Prob, a)])
importance' i s pv' =
  case cs of
    [] -> return vs
    _  -> 
      do
        r <- getStdRandom random
        let target = r * csum
        fmap (vs ++) $ importance' i (s*csum) (accum 0 target cs)
  where
    pv = explore' (Just i) pv'
    vs = [(s*p, v) | (p, V v) <- pv]
    cs  = [(p, c) | (p, C c) <- pv, length c /= 0]
    csum = sum (map fst cs)

importanceSamples' :: (Ord a) => Int -> [(Prob, a)] -> Q a -> Int -> IO [(Prob, a)]
importanceSamples' _ pv comp 0 = return $ undup pv
importanceSamples' i pv comp n =
  do
    r <- importance' i 1.0 (reify0 comp)
    importanceSamples' i (r ++ pv) comp (n-1)


[handler|
  forward h.
    SampleLoop a :: Comp (SampleLoop h a) a -> a
      polyhandles {Failure} where
        Failure  k comp -> sampleLoop comp comp
        Return x   _    -> return x
|]

sample :: (h `Handles` Rand, h `PolyHandles` Failure) => Q a -> Comp h a 
sample comp = sampleHandler comp

sampleLoop' :: Q a -> IO a
sampleLoop' comp = handleIO (sampleLoop (sample comp) (sample comp))

instance IOHandler a `Handles` Rand where
  clause Rand k h =
    do
      r <- getStdRandom random
      k r h

samples :: Ord a => Q a -> Int -> IO [(Prob, a)]
samples comp n =
  (handleIO (exploreHandler'
             (do
                 let l = take n (repeat (1/(fromIntegral n), ()))
                 dist l
                 sample comp)))


importanceSamples :: Ord a => Int -> Q a -> Int -> IO [(Prob, a)]
importanceSamples i comp n =
  handleIO (exploreHandler'
            (do
                let l = take n (repeat (1/(fromIntegral n), ()))
                dist l
                importanceSample i comp))


drunkCoin :: Q Bool
drunkCoin =
  do
    t <- toss 0.5
    lost <- toss 0.9
    if lost then failure else return t
 
dcoinAnd :: Int -> Q Bool
dcoinAnd 1 = drunkCoin
dcoinAnd n = drunkCoin &&& dcoinAnd (n-1)
