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
    DataKinds,
    PolyKinds,
    TypeOperators,
    ScopedTypeVariables #-}

{- This is a handlers port of Jeff Newbern's example illustrating
lifting for a stack of monads transformers.

In the handler version, all of the calls to lift disappear. There is
no need to worry about the order of the handlers when writing an
abstract computation.

Other differences:

 * The type signatures for functions become more precise, listing only
the operations that are used.

 * It is necessary to introduce a Choose operation for selecting an
element of a list.

-}

{- Author: Jeff Newbern
Maintainer: Jeff Newbern <jnewbern@nomaware.com>
Time-stamp: <Mon Aug 18 14:51:56 2003>
License: GPL
-}

{- DESCRIPTION

Example 26 - Managing a complex transformer stack.

Usage: Compile the code (with -fglasgow-exts) and run it.
It will print a series of (value,log) pairs.
The output isn't very interesting, but you should try to understand
in detail how the different monadic computations in the source
below interact to produce the values.

Try: ./ex26
-}

import Handlers
import TopLevel
import DesugarHandlers

import Control.Monad
import Data.Char (digitToInt)
--import Control.Monad.State
--import Control.Monad.Writer

import Data.Monoid

[operation|forall a.Choose :: [a] -> a|]
-- big fat memory leak!
[handler|
  forward h.AllResultsLeaky a :: [a]
    handles {Choose} where
      Return x   -> return [x]
      Choose l k -> liftM concat (mapM k l)
|]
[handler|
  forward h.AllResults a :: [a]
    handles {Choose} where
      Return x       -> return [x]
      Choose l     k -> step l []
                        where
                          step []     rs = return rs
                          step (x:xs) rs = do {ys <- k x; step xs (rs ++ ys)}
|]

[operation|Get s :: s|]
[operation|Put s :: s -> ()|]

[operation|Tell s :: s -> ()|]
[operation|Listen h s a :: Comp h a -> (a, s)|] 

type SComp s a =
  ((h `Handles` Get) s, (h `Handles` Put) s) => Comp h a

[handler|
  forward h.
    RunState s a :: s -> (a, s)
      handles {Get s, Put s} where
        Return  x     s -> return (x, s)
        Get        k  s -> k s  s
        Put     s  k  _ -> k () s
|] 
[handler| 
  forward h.
    EvalState s a :: s -> a 
      handles {Get s, Put s} where
        Return  x     _ -> return x
        Get        k  s -> k s  s
        Put     s  k  _ -> k () s
|]

[handler| 
  forward h.(Monoid s) =>
    RunWriter s a :: s -> (a, s)
      handles {Tell s, Listen (RunWriter h s a) s a} where
        Return  x      s -> return (x, s)
        Tell    s'  k  s -> k () (s `mappend` s')
        Listen  c   k  s -> do (v, s') <- runWriter' c; k (v, s') (s `mappend` s')
|]
runWriter' comp = runWriter mempty comp
[handler|
  forward h.(Monoid s) =>
    EvalWriter s a :: s -> a
      handles {Tell s, Listen (RunWriter h s a) s a} where
        Return  x      _ -> return x
        Tell    s'  k  s -> k () (s `mappend` s')
        Listen  c   k  s -> do (v, s') <- runWriter' c; k (v, s') (s `mappend` s')
|]
evalWriter' comp = evalWriter mempty comp
[handler|
  IoStringWriter a :: IO a
    handles {Tell (String), Listen (RunWriter (HandlePure (a, String)) (String) a) (String) a} where
      Return  x      -> return x
      Tell    s   k  -> do putStr s; k ()
      Listen  c   k  -> k (handlePure (runWriter' c))
|]

-- -- this is our combined monad type for this problem
-- type NDS a = StateT Int (WriterT [String] []) a

{- Here is a computation on lists -}

-- return the digits of a number as a list
getDigits :: Int -> [Int]
getDigits n = let s = (show n)
              in map digitToInt s

{- Here are some computations in MonadWriter -}

-- write a value to a log and return that value
--logVal :: (MonadWriter [String] m) => Int -> m Int
logVal :: ([handles|h {Tell ([String])}|]) => Int -> Comp h Int
logVal n = do tell ["logVal: " ++ (show n)]
              return n

-- -- do a logging computation and return the length of the log it wrote
-- getLogLength :: (MonadWriter [[a]] m) => m b -> m Int
-- getLogLength c = do (_,l) <- listen $ c
--getLogLength :: ([handles|h' {Listen h ([String]) a}|]) => Comp h a -> Comp h' Int
getLogLength :: (Handles h' Listen '(h, [[b]], a)) => Comp h a -> Comp h' Int
getLogLength c = do (_,l) <- listen c 
                    return (length (concat l))

-- -- log a string value and return 0
-- logString :: (MonadWriter [String] m) => String -> m Int
logString :: ([handles|h {Tell ([String])}|]) => String -> Comp h Int
logString s = do tell ["logString: " ++ s]
                 return 0

-- {- Here is a computation that requires a WriterT [String] [] -}

-- -- "Fork" the computation and log each list item in a different branch.
-- logEach :: (Show a) => [a] -> WriterT [String] [] a
-- logEach xs = do x <- lift xs
logEach :: ([handles|h {Tell ([String])}|], [handles|h {Choose}|], Show a) => [a] -> Comp h a
logEach xs = do x <- choose xs
                tell ["logEach: " ++ (show x)]
                return x


-- {- Here is a computation in MonadState -}

-- -- increment the state by a specified value
-- addVal :: (MonadState Int m) => Int -> m ()
addVal :: ([handles|h {Get (Int)}|], [handles|h {Put (Int)}|]) => Int -> Comp h ()
addVal n = do x <- get
              put (x+n)

-- {- Here are some computations in the combined monad -}

-- -- set the state to a given value, and log that value
-- setVal :: Int -> NDS ()
-- setVal n = do x <- lift $ logVal n
setVal :: ([handles|h {Tell ([String])}|], [handles|h {Put (Int)}|]) => Int -> Comp h ()
setVal n = do x <- logVal n
              put x

-- -- "Fork" the computation, adding a different digit to the state in each branch.
-- -- Because setVal is used, the new values are logged as well.
-- addDigits :: Int -> NDS ()
-- addDigits n = do x <- get
--                  y <- lift . lift $ getDigits n
--                  setVal (x+y)
addDigits :: ([handles|h {Tell ([String])}|], [handles|h {Choose}|], [handles|h {Get (Int)}|], [handles|h {Put (Int)}|]) =>
               Int -> Comp h ()
addDigits n = do x <- get
                 y <- choose (getDigits n)
                 setVal (x+y)


-- {- an equivalent construction is:
-- addDigits :: Int -> NDS ()
-- addDigits n = do x <- get
-- msum (map (\i->setVal (x+i)) (getDigits n))
-- -}

-- {- This is an example of a helper function that can be used to put all of the lifting logic
-- in one location and provide more informative names. This has the advantage that if the
-- transformer stack changes in the future (say, to add ErrorT) the changes to the existing
-- lifting logic are confined to a small number of functions.
-- -}
-- liftListToNDS :: [a] -> NDS a
-- liftListToNDS = lift . lift

-- -- perform a series of computations in the combined monad, lifting computations from other
-- -- monads as necessary.
main :: IO ()
-- main = do mapM_ print $ runWriterT $ (`evalStateT` 0) $ do x <- lift $ getLogLength $ logString "hello"
--                                                            addDigits x
--                                                            x <- lift $ logEach [1,3,5]
--                                                            lift $ logVal x
--                                                            liftListToNDS $ getDigits 287
main = do mapM_ print (handlePure (allResults (runWriter' (evalState 0 test))))
       where
         test = do x <- getLogLength (logString "hello")
                   addDigits x
                   y <- logEach [1,3,5]
                   logVal y
                   choose (getDigits 287)


