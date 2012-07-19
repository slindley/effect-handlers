-- Choosing food. A somewhat contrived example from the draft paper:
--
--   http://homepages.inf.ed.ac.uk/slindley/papers/handlers.pdf

{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction,
             FlexibleContexts, TypeOperators #-}

import Control.Monad
import Control.Monad.Identity
import Control.Monad.List
import Control.Monad.Trans
import System.Random

import Handlers

randBool :: IO Bool
randBool  = getStdRandom random

-- the basic computation models the choice of a fruit ("apple" or
-- "orange") along with a form ("raw" or "cooked")
chooseFood :: Monad m => m Bool -> m String
chooseFood choose =
  do
    x <- choose
    let fruit = if x then "apple" else "orange"
    y <- choose
    let form = if y then "raw " else "cooked "
    return (form ++ fruit)

----- standard monadic approach

-- probabilistic choice
runProb :: IO String
runProb =
  chooseFood randBool

-- deterministic choice
runTrue :: String
runTrue =
  runIdentity $ chooseFood (return True)

-- nondeterministic choice
runAll :: [String]
runAll =
  chooseFood ([True, False])


-- allow each choice to be interpretted differently
chooseFood2 :: Monad m => m Bool -> m Bool -> m String
chooseFood2 choose1 choose2 =
  do
    x <- choose1
    let fruit = if x then "apple" else "orange"
    y <- choose2
    let form = if y then "raw" else "cooked"
    return (form ++ " " ++ fruit)

----- standard monadic approach
    
    
runProbProb :: IO String
runProbProb = chooseFood2 (getStdRandom random) (getStdRandom random)

-- combining probability and nondeterminism using a monad transformer

runProbAll :: IO [String]
runProbAll = runListT $ chooseFood2 (ListT (return [True, False])) (lift $ getStdRandom random)

runAllProb :: IO [String]
runAllProb = runListT $ chooseFood2 (lift $ getStdRandom random) (ListT (return [True, False]))


----- using effect handlers

data Choice = Choice
instance Op Choice where
  type Param Choice = ()
  type Return Choice = Bool
choice = applyOp Choice ()

handleProb :: IO String
handleProb =
  handle (chooseFood choice)
         (Choice |-> (\p k -> do {v <- randBool; k v}) :<: Empty,
          return)

handleTrue :: Identity String
handleTrue =
  handle (chooseFood choice)
         (Choice |-> (\p k -> k True) :<: Empty,
          return)

handleAll :: [String]
handleAll =
  handle (chooseFood choice)
         (Choice |-> (\p k -> k True ++ k False) :<: Empty,
          return)

data Choice1 = Choice1
instance Op Choice1 where
  type Param Choice1 = ()
  type Return Choice1 = Bool
choice1 = applyOp Choice1 ()

data Choice2 = Choice2
instance Op Choice2 where
  type Param Choice2 = ()
  type Return Choice2 = Bool
choice2 = applyOp Choice2 ()

-- horizontal composition of nondeterminism and probability
handleAllProbH :: IO [String]
handleAllProbH =
  handle (chooseFood2 choice1 choice2)
         (    Choice1 |-> (\p k -> do xs <- k True;
                                      ys <- k False;
                                      return (xs ++ ys))
          :<: Choice2 |-> (\p k -> do {v <- randBool; k v})
          :<: Empty,
          \x -> return [x])

-- vertical composition of nondeterminism and probability
handleAllProbV :: IO [String]
handleAllProbV =
  handle
    (handle (chooseFood2 choice1 choice2)
            (Choice1 |-> (\p k -> do {xs <- k True; ys <- k False; return (xs ++ ys)}) :<: Choice2 -:<: Empty,
             \x -> return [x]))
    (Choice2 |-> (\p k -> do {v <- randBool; k v}) :<: Empty,
     return)

