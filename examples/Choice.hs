{-# LANGUAGE TypeFamilies,
    GADTs,
    NoMonomorphismRestriction,
    RankNTypes,
    MultiParamTypeClasses,
    QuasiQuotes,
    FlexibleInstances,
    FlexibleContexts,
    OverlappingInstances,
    UndecidableInstances,
    ConstraintKinds,
    TypeOperators,
    ScopedTypeVariables #-}

import Control.Monad
import System.Random
import Handlers
-- import TopLevel
import DesugarHandlers

[handler|
  HandlePure a :: a handles {} where
    Return x -> x
|]

[operation|forall a.Choose  :: a -> a -> a|]
[operation|forall a.Failure :: a |]
[operation|Rand             :: Double|]

[handler|
  AllResults a :: [a] handles {Choose, Failure} where
    Return x     -> [x]
    Choose x y k -> k x ++ k y
    Failure    k -> []
|]

[handler|
  forward h handles {Rand}.
    RandomResult a :: a handles {Choose} where
      Return x     -> return x
      Choose x y k -> do {r <- rand;
                          k (if r < 0.5 then x else y)}
|]

[handler|
  forward h.
    Persevere a :: Comp (Persevere h a) a -> a handles {Failure} where
      Return  x _ -> return x
      Failure k c -> persevere c c
|]

[handler|
  forward h.
    MaybeResult a :: Maybe a handles {Failure} where
      Return  x -> return (Just x)
      Failure k -> return Nothing
|]

[handler|
  RandomHandler a :: IO a handles {Rand} where
    Return x -> return x
    Rand   k -> do {r <- getStdRandom random; k r}
|]

-- allResults (drunkCoins 3)
-- randomHandler ((maybeResult . randomResult) (drunkCoins 3))
-- let c = randomResult (drunkCoins 3) in randomHandler (persevere c c)

data Outcome = Caught | Dropped
data Toss    = Heads | Tails deriving Show
drunkCoin = do {outcome <- choose Caught Dropped;
                case outcome of
                  Caught  -> choose Heads Tails
                  Dropped -> failure}
drunkCoins n = replicateM n drunkCoin
             



-- [handler|
--   forward h handles {Failure}.
--     FirstResult a :: a handles {Choose} where
--       Return x     -> return x
--       Choose x y k -> fallBackHandler (k y) (k x)
-- |]

-- [handler|
--   forward h.
--     FallBackHandler a :: (Comp h a) -> a handles {Failure} where
--       Return x   _ -> return x
--       Failure  k c -> c
-- |]



-- --[operation|Toss :: Bool|]



-- -- type SComp s a =
-- --   ((h `Handles` Get) s, (h `Handles` Put) s) => Comp h a

-- -- [handler|
-- --   MonadicState s a :: s -> (a, s)
-- --     handles {Get s, Put s} where
-- --       Return  x     s -> (x, s)
-- --       Get        k  s -> k s  s
-- --       Put     s  k  _ -> k () s
-- -- |] 
