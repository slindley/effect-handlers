-- state using McBride handlers

{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction,
             FlexibleContexts, TypeOperators #-}

import McBrideHandlers

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
                    OpHandler e (Comp (Get s, (Put s, e)) a) (m a) -> s -> Comp (Get s, (Put s, e)) a -> m a
handleStateWith h s comp =
  handle comp
  (Get |-> (\() k -> handleStateWith h s $ k s)  :<:
   Put |-> (\s  k -> handleStateWith h s $ k ()) :<: h,
   return)


