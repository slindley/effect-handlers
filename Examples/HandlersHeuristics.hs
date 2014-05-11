{-# LANGUAGE TypeOperators,TypeFamilies,
    GADTs,
    RankNTypes,
    MultiParamTypeClasses,
    QuasiQuotes,
    FlexibleInstances,
    FlexibleContexts,
    OverlappingInstances,
    UndecidableInstances,
    PolyKinds,
    ConstraintKinds #-}

module Examples.HandlersHeuristics where

import Prelude hiding (fail)
import Control.Monad (when)

import Handlers
import Data.IORef
import DesugarHandlers
import Examples.HandlersMonadRef

-- Prolog interface
[operation| Toss :: Bool|]
[operation| forall a. Fail :: a|]

(|||) t1 t2 = do {r <- toss; if r then t1 else t2}


-- Copy/pasted Prolog challenge, sans types ----
queens n = go [1..n] []
  where go [] acc = return acc
        go l  acc = do (n,l') <- select l
                       guard (noThreat acc n 1)
                       go l' (n:acc)
select []      =  fail
select (x:xs)  =  return (x,xs) |||
                  do  (y,ys) <- select xs
                      return (y,x:ys)

noThreat :: [Int] -> Int -> Int -> Bool
noThreat []      r c  = True
noThreat (m:ms)  r c  = abs (m - r) /= c && noThreat ms r (c+1)

guard True   =  return ()
guard False  =  fail
------------------------------------------------

type Tree a = [handles| h {Toss}|] => Comp h a
type Heuristic a = Tree a -> Tree a

[handler| forward h handles {Toss, Fail} .
          Dbs a :: Int -> a
          handles {Toss} where
            Return x n -> return x
            Toss k 0 -> fail
            Toss k n -> k True (n-1) ||| k False (n-1)
 |]

[handler|forward h .
 ListProlog a :: [a]
   handles {Toss, Fail} where
     Return x -> return [x]
     Fail k -> return []
     Toss k -> do r1 <- k True
                  r2 <- k False
                  return (r1++r2)
 |]

[handler|
 forward h handles {Toss, Fail} .
 Dibs a :: Int -> a
 handles {Toss} where
   Return x n -> return x
   Toss k 0 -> fail
   Toss k n -> k True n ||| k True (n - 1)
 |]

-- A subtlety in the TemplateHaskell implementation: because we pass a
-- concrete type as argument to the effects, Int need to be
-- paranthesized.
[handler|
 forward h handles {Toss, Fail, ReadRef (Int), WriteRef (Int)} .
 NbsHandler a :: (Ref Int) -> a
 handles {Toss} where
   Return x r -> return x
   Toss k r -> do n <- modifyRef r pred
                  guard (n > 0)
                  k True r ||| k False r
 |]

nbs n comp = do r <- newRef n
                nbsHandler r comp

-- To be faithful to the example, we want to write this code:
-- [handler|
--  forward h handles
--    {Toss, Fail,
--     ReadRef (Int), WriteRef (Int),
--     ReadRef (Bool), WriteRef (Bool)}.

--  FbsHandler a :: (Ref Int) -> (Ref Bool) -> a
--  handles {Toss} where
--    Return x r fr -> return x
--    Toss k r fr -> k True r fr ||| do b <- modifyRef fr (const False)
--                                      when (not b)
--                                        (do n <- modifyRef r pred
--                                            guard (n > 0))
--                                      k False r fr
--  |]
--
-- fbs n comp = do r <- newRef n
--                 fr<- newRef False
--                 x <- fbsHandler r fr comp
--                 writeRef fr True
--                 return x
--
-- Which results in an error because the handler library cannot deal
-- with overloading of effect operations (even at different types).

-- tests
test1 = listProlog (queens 8)
test2 = listProlog (dbs  20 (queens 8))
test3 = listProlog (dibs 20 (queens 8))
test4 = iORefState (listProlog (nbs 1800 (queens 8)))
