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

module HandlersHeuristics where

import Prelude hiding (fail)
import Control.Monad (when)

import ShallowFreeHandlers
import Data.IORef
import DesugarHandlers


-- The entwine operator really looks like a shallow handler, and
-- indeed it has a straightforward implementation as one (see the
-- ShallowPipes example in the 'handlers in action' paper.)


[shallowHandler| forward h handles {Toss} . 
          EntwineLeft a :: Comp (EntwineRight h a) a -> a
          handles {Toss} where
            Return y _ -> return y
            Toss k right -> entwineRight (k True) (k False) right
         |]

[shallowHandler| forward h handles {Toss}.
  EntwineRight a :: Comp (EntwineLeft h a) a -> Comp (EntwineLeft h a) a -> a 
  handles {Toss} where
  Return x _ _ -> return x
  Toss k x1 x2 -> (entwineLeft (k True) x1) ||| (entwineLeft (k False) x2)
 |]

p \|/ q = entwineLeft q p


-- We can now copy paste from Heuristics.hs.

-- BTW, there was a mistake in the original file where the ||| in
-- dibsTree below was a \|/. This error was caught by the typechecker,
-- which is another advantage of using this Handler library.
dibs' db t = t \|/ dibsTree db where
  dibsTree 0  = fail
  dibsTree n  = dibsTree n ||| dibsTree (n-1)
  
nbs' n t  =  do  ref <- newRef n
                 t \|/ nbsTree ref where
                   nbsTree ref = do  n <- modifyRef ref pred
                                     guard (n > 0)
                                     nbsTree ref ||| nbsTree ref
  
-- Can't do FBS, as discussed before. 

delay 0  =  return ()
delay n  =  delay (n-1) ||| delay (n-1)

itd t  =  do  newRef False >>= go t 0 where
    go t n ref  =    (t \|/ (delay n >> prune ref)) |||
                       do  b <- readRef ref
                           if b  then  do  writeRef ref False
                                           go t (n+1) ref
                                 else  fail
    prune ref  =  writeRef ref True >> fail

  
-- Writing this review is starting to take quite a long while, so I
-- did not get around to implementing the muddle example. I am happy
-- to take this `offline' after the reviews are due and discuss it
-- in private.

test5 = iORefState (listProlog (dibs' 20 (queens 8)))
test6 = iORefState (listProlog (nbs' 1800 (queens 8)))
test7 = iORefState (listProlog (itd (queens 8)))















--- Copy/paste from previous files to make this file standalone
----as Handlers and ShallowHandlers don't play well together ---------

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

type Ref a = IORef a

[operation|NewRef   s ::     s      -> Ref s |]
[operation|ReadRef  s :: Ref s      -> s     |]
[operation|WriteRef s :: Ref s -> s -> ()    |]

type RWComp s a = ([handles|h {ReadRef s}|], [handles| h {WriteRef s}|]) => Comp h a
type RefComp s a =
  ([handles|h {NewRef s}|]
  ,[handles|h {ReadRef s}|]
  ,[handles|h {WriteRef s}|]) => Comp h a

--modifyRef :: Ref a -> (a -> a) -> RWComp a a
modifyRef r f = do x <- readRef r
                   writeRef r (f x)
                   return x

[shallowHandler|
 IORefState s a :: IO a
   handles {NewRef s, ReadRef s, WriteRef s} where
     Return x -> return x
     NewRef   s   k -> do r <- newIORef s
                          iORefState (k r)
     ReadRef  r   k -> do s <- readIORef r
                          iORefState (k s)
     WriteRef r s k -> do writeIORef r s
                          iORefState (k ())
 |]

--------------------------------------------------

[shallowHandler| forward h.
 ListProlog a :: [a]
   handles {Toss, Fail} where
     Return x ->  return [x]
     Fail k -> return []
     Toss k -> do r1 <- listProlog (k True) 
                  r2 <- listProlog (k False)
                  return (r1++r2)
 |]

--------------------------------------------------
--  End of Copy/Paste ----------------------------
--------------------------------------------------


