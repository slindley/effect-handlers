{-# LANGUAGE TypeFamilies,
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
import Data.IORef
import PolyHandlers
import DesugarPolyHandlers

[operation|Get s :: s|]
[operation|Put s :: s -> ()|]

type SComp s a =
  ((h `Handles` Get) s, (h `Handles` Put) s) => Comp h a

[handler|
  MonadicState s a :: s -> (a, s)
    handles {Get s, Put s} where
      Return  x     s -> (x, s)
      Get        k  s -> k s  s
      Put     s  k  _ -> k () s
|] 
[handler|
  SimpleState s a :: s -> a 
    handles {Get s, Put s} where
      Return  x     _ -> x
      Get        k  s -> k s  s
      Put     s  k  _ -> k () s
|]
[handler|
  LogState s a :: [s] -> (a, [s])
    handles {Get s, Put s} where
      Return  x      ss     -> (x, tail (reverse ss))
      Get         k  (s:ss) -> k s  (s:ss)
      Put     s   k  ss     -> k () (s:ss)
|]
[handler|
  IORefState s a :: IORef s -> IO a
    handles {Get s, Put s} where
      Return  x     _ -> return x
      Get        k  r -> do {s <- readIORef r; k s r}
      Put     s  k  r -> do {writeIORef r s; k () r}
|]


[handler|
  forward h.ForwardState s a :: s -> a 
    handles {Get s, Put s} where
      Return  x     _ -> return x
      Get        k  s -> k s  s
      Put     s  k  _ -> k () s
|]
type SComp1 h f s a =
  ((h' `Handles` Get) s, (h' `Handles` Put) s, f h s a ~ h') => Comp h' a
--forwardState' :: s -> SComp1 h ForwardState s a -> Comp h a  -- (Handles h Get s, Handles h Put s, h ~ ForwardState h' s a) => s -> Comp h a -> Comp h' a
forwardState' :: s -> SComp' (ForwardState h s a) s a -> Comp h a
forwardState' s c = forwardState s c
[operation|LogPut s :: s -> ()|]
[handler|
  forward h.(Handles h Get s, Handles h Put s, Handles h LogPut s) =>
    PutLogger s a :: a
      handles {Put s} where
        Return  x     -> return x
        Put     s   k -> do {logPut s; put s; k ()}
|]
[handler|
  forward h.
    LogPutReturner s a :: (a, [s])
      handles {LogPut s} where
        Return x   -> return (x, [])
        LogPut s k -> do {(x, ss) <- k (); return (x, s:ss)}
|]
[handler|
  forward h.(Handles h PrintLine Unit, Show s) =>
    LogPutPrinter s a :: a
      handles {LogPut s} where
        Return x   -> return x
        LogPut s k -> do {printLine ("Put: " ++ show s); k ()}
|]

[operation|PrintLine :: String -> ()|]
instance (IOHandler a `Handles` PrintLine) () where
  clause (PrintLine s) k h =
    do
      putStrLn s
      k () h

stateWithLog :: s -> SComp s a -> (a, [s]) 
stateWithLog s comp = (handlePure . logPutReturner . forwardState s . putLogger) comp

statePrintLog :: Show s => s -> SComp s a -> IO a 
statePrintLog s comp = (handleIO . logPutPrinter . forwardState s . putLogger) comp

--putLogger :: SComp s a -> ((h `Handles` LogPut) s) => SComp' h s a
--putLogger :: (((h `Handles` LogPut) s) => SComp' h s a) -> ((h `Handles` LogPut) s) => SComp' h s a

type SComp' h s a =
  ((h `Handles` Get) s, (h `Handles` Put) s) => Comp h a


-- foo :: SComp' h s a -> ()
-- foo _ = ()

[operation|forall a.Err :: String -> a|]
[handler|
  ReportErr a :: Either String a
    handles {Err} where
      Return x   -> Right x
      Err m    k -> Left m      |] 

stateErr s = reportErr . forwardState s

type SEComp s a =
  ((h `Handles` Get) s, (h `Handles` Put) s, (h `Handles` Err) ()) =>
     Comp h a

comp2 :: SEComp Int Int
comp2 = do {x <- get; if x == 0 then err "division by zero"
                      else put (256 `div` x); y <- get; return (y+16)}



comp0 :: SComp String String
comp0 = do {  x <- get; put ("zig-" ++ x);
              y <- get; put (y ++ ":" ++ y); get}
testa = monadicState "zag"   comp0
testb = simpleState  "zag"   comp0
testc = logState     ["zag"] comp0
testd = do {r <- newIORef "zag"; iORefState r comp0}

comp1 :: SComp Int Int
comp1 = do {  x <- get; put (x+1);
              y <- get; put (y+y); get}

test1 = monadicState 1 comp1
test2 = simpleState 1 comp1
test3 = logState [1] comp1
test4 = do {r <- newIORef 1; iORefState r comp1}

-- *Main> monadicState 1 comp1
-- (4, 4)

-- *Main> simpleState 1 comp1
-- 4

-- *Main> logState [] 1 comp1
-- (4, [1, 2, 4])

-- *Main> do {r <- newIORef 1; iORefState r comp1}
-- 4
