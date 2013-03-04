-- state using parameterised handlers

{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction,
             FlexibleContexts, TypeOperators, ScopedTypeVariables #-}

import ParameterisedHandlers

data Get s = Get
instance Op (Get s) where
  type Param  (Get s) = ()
  type Return (Get s) = s
get = applyOp Get

data Put s = Put
instance Op (Put s) where
  type Param  (Put s) = s
  type Return (Put s) = ()
put = applyOp Put

-- handle state in the standard way
handleState :: Monad m => s -> Comp (Get s, (Put s, ())) a -> m a
handleState = handleStateWith Empty

-- The handleStateWith function generalises handleState to support
-- horizontal composition, either for throwing other effects or for
-- composing with compatible effects such as random choice.
handleStateWith :: (Get s `NotIn` e, Put s `NotIn` e, Monad m) =>
                    OpHandler e (m a) s -> s -> Comp (Get s, (Put s, e)) a -> m a
handleStateWith h s comp =
  handle s comp
  (Get |-> (\() k -> k s s)  :<:
   Put |-> (\s  k -> k s ()) :<: h,
   return)

data Mode = Handle | Forward

mcbrideState mode (s :: Int) comp =
  handle mode comp
  ((Get |->
    case mode of
      Handle ->
        (\() k -> mcbrideState Forward s (k Forward s))
      Forward ->
        (\p k -> App makeWitness Get p (k Forward))) :<:
   (Put |->
    case mode of
      Handle ->
        (\s k -> mcbrideState Forward s (k Forward ()))
      Forward ->
        (\p k -> App makeWitness Put p (k Forward))) :<: Empty,
   return)

getInt :: In (Get Int) e => () -> Comp e Int
getInt = get

putInt :: In (Put Int) e => Int -> Comp e ()
putInt = put

count :: Comp (Get Int, (Put Int, ())) ()
count =
    do {n <- get ();
        if n == (0 :: Int) then return ()
        else do {put (n-1); count}}
