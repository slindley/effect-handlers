{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

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

import Control.Monad
import Data.Char (digitToInt)
import Control.Monad.State
import Control.Monad.Writer

-- this is our combined monad type for this problem
type NDS a = StateT Int (WriterT [String] []) a

{- Here is a computation on lists -}

-- return the digits of a number as a list
getDigits :: Int -> [Int]
getDigits n = let s = (show n)
              in map digitToInt s

{- Here are some computations in MonadWriter -}

-- write a value to a log and return that value
logVal :: (MonadWriter [String] m) => Int -> m Int
logVal n = do tell ["logVal: " ++ (show n)]
              return n

-- do a logging computation and return the length of the log it wrote
getLogLength :: (MonadWriter [[a]] m) => m b -> m Int
getLogLength c = do (_,l) <- listen $ c
                    return (length (concat l))

-- log a string value and return 0
logString :: (MonadWriter [String] m) => String -> m Int
logString s = do tell ["logString: " ++ s]
                 return 0

{- Here is a computation that requires a WriterT [String] [] -}

-- "Fork" the computation and log each list item in a different branch.
logEach :: (Show a) => [a] -> WriterT [String] [] a
logEach xs = do x <- lift xs
                tell ["logEach: " ++ (show x)]
                return x

{- Here is a computation in MonadState -}

-- increment the state by a specified value
addVal :: (MonadState Int m) => Int -> m ()
addVal n = do x <- get
              put (x+n)

{- Here are some computations in the combined monad -}

-- set the state to a given value, and log that value
setVal :: Int -> NDS ()
setVal n = do x <- lift $ logVal n
              put x

-- "Fork" the computation, adding a different digit to the state in each branch.
-- Because setVal is used, the new values are logged as well.
addDigits :: Int -> NDS ()
addDigits n = do x <- get
                 y <- lift . lift $ getDigits n
                 setVal (x+y)

{- an equivalent construction is:
addDigits :: Int -> NDS ()
addDigits n = do x <- get
msum (map (\i->setVal (x+i)) (getDigits n))
-}

{- This is an example of a helper function that can be used to put all of the lifting logic
in one location and provide more informative names. This has the advantage that if the
transformer stack changes in the future (say, to add ErrorT) the changes to the existing
lifting logic are confined to a small number of functions.
-}
liftListToNDS :: [a] -> NDS a
liftListToNDS = lift . lift

-- perform a series of computations in the combined monad, lifting computations from other
-- monads as necessary.
main :: IO ()
main = do mapM_ print $ runWriterT $ (`evalStateT` 0) $ do x <- lift $ getLogLength $ logString "hello"
                                                           addDigits x
                                                           x <- lift $ logEach [1,3,5]
                                                           lift $ logVal x
                                                           liftListToNDS $ getDigits 287

-- END OF FILE
