{-# LANGUAGE TypeFamilies,
    GADTs,
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
import Handlers
import TopLevel
import DesugarHandlers

import Criterion.Main
import Criterion.Config

[operation|Get s :: s|]
[operation|Put s :: s -> ()|]

type SComp s a =
  ([handles|h {Get s}|], [handles|h {Put s}|]) => Comp h a

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


-- Oops!
--
-- The following doesn't work because we need a type constraint
-- [|handles|h {Err}|] and we currently have no way of writing it.
--
-- [handler|
--   forall h handles {Err}.ForwardState0 h s a :: s -> Comp h a
--     handles {Get s, Put s, Err} where
--       Return  x     _ -> return x
--       Get        k  s -> k s  s
--       Put     s  k  _ -> k () s
--       Err     m  k  s -> do {x <- err m; k x s}
-- |]
--
-- Here's one (rather ugly) fix:
newtype WrappedComp h c a = Wrap {unWrap :: c => Comp h a}
type WrappedErrComp h a = WrappedComp h [handles|h {Err}|] a
[handler|
  ForwardState0 h s a :: s -> WrappedErrComp h a
    handles {Get s, Put s, Err} where
      Return  x     _ -> Wrap (return x)
      Get        k  s -> k s  s
      Put     s  k  _ -> k () s
      Err     m  k  s -> Wrap (do {x <- err m; unWrap (k x s)})
|]

[handler|
  forward h.ForwardState s a :: s -> a 
    handles {Get s, Put s} where
      Return  x     _ -> return x
      Get        k  s -> k s  s
      Put     s  k  _ -> k () s
|]
-- data ForwardState h s a = ForwardState s
-- type instance Result (Forward h s a) = Comp h a
-- instance (ForwardState h s a `Handles` Get) s where
--     clause Get k' (ForwardState s) = k s s
--         where
--           k v s = k' v (ForwardState s)
-- instance (h `Handles` op) t => (ForwardState h s a `Handles` op) t where
--     clause op k h = do {x <- doOp op; k x h}

-- forwardState :: s -> Comp (ForwardState h s a) a -> Comp h a
-- forwardState :: (h `Handles` {Get, Put | e}, parent `Handles` {|e}) -> Comp h a -> Comp parent a

[operation|LogPut s :: s -> ()|]
[handler|
  forward h handles {Put s, LogPut s}.
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
  forward h handles {PrintLine}.(Show s) =>
    LogPutPrinter s a :: a
      handles {LogPut s} where
        Return x   -> return x
        LogPut s k -> do {printLine ("Put: " ++ show s); k ()}
|]

[operation|PrintLine :: String -> ()|]
[handler|
  PrintHandler a :: IO a handles {PrintLine} where
    Return x      -> return x
    PrintLine s k -> do {putStrLn s; k ()}
|]

stateWithLog :: s -> SComp s a -> (a, [s])
stateWithLog s comp = handlePure ((logPutReturner . forwardState s . putLogger) comp)

statePrintLog :: Show s => s -> SComp s a -> IO a 
statePrintLog s comp = printHandler ((logPutPrinter . forwardState s . putLogger) comp)

--putLogger :: SComp s a -> ((h `Handles` LogPut) s) => SComp' h s a
--putLogger :: (((h `Handles` LogPut) s) => SComp' h s a) -> ((h `Handles` LogPut) s) => SComp' h s a

type SComp' h s a =
  ([handles|h {Get s}|], [handles|h {Put s}|]) => Comp h a

[operation|forall a.Err :: String -> a|]
[handler|
  ReportErr a :: Either String a
    handles {Err} where
      Return x   -> Right x
      Err m    k -> Left m      |] 

stateErr s = reportErr . forwardState s

type SEComp s a =
  ([handles|h {Get s}|], [handles|h {Put s}|], [handles|h {Err}|]) =>
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

count :: SComp Int Int
count =
    do {i <- get;
        if i == 0 then return i
        else do {put (i-1); count}}


-- test5 = print (simpleState 100000000 count)
-- test6 = printHandler (forwardState 100000000 count)

-- main = test6

test5 = simpleState  1000000000
test6 = forwardState 1000000000
-- lets not bother with IORefs - they're too slow
test7 comp = do r <- newIORef 1000000000; iORefState r comp

main = defaultMain [
         bcompare [ bench "simple"  $ whnf test5 count
                  , bench "forward" $ whnf test6 count ]]

-- test5: 10.1 seconds
-- test6: 10.1 seconds
