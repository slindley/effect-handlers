{-# LANGUAGE TypeFamilies,
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

module Examples.HandlersMonadRef where

import Handlers
import Data.IORef
import DesugarHandlers

-- I'm cheating here: our references coincide exactly with
-- IORef. Presumably one can do something slightly more sophisticated
-- to obtain the same level of generality as in the submission
type Ref a = IORef a

[operation|NewRef   s ::     s      -> Ref s |]
[operation|ReadRef  s :: Ref s      -> s     |]
[operation|WriteRef s :: Ref s -> s -> ()    |]

type RWComp s a = ([handles|h {ReadRef s}|], [handles| h {WriteRef s}|]) => Comp h a
type RefComp s a =
  ([handles|h {NewRef s}|]
  ,[handles|h {ReadRef s}|]
  ,[handles|h {WriteRef s}|]) => Comp h a

modifyRef r f = do x <- readRef r
                   writeRef r (f x)
                   return x

[handler|
 forward h handles {NewRef s}.
  CountRefHandler s a :: Int -> (a,Int)
    handles {NewRef s} where
      Return x c -> return (x,c)
      NewRef s k c -> do r <- newRef s
                         k r (c+1)
|]

-- The abstraction leaks here (see the 'handlers in action' paper).
countRef :: Comp (CountRefHandler h s a) a -> Comp h (a, Int)
countRef comp = countRefHandler 0 comp

[handler|
 IORefState s a :: IO a
   handles {NewRef s, ReadRef s, WriteRef s} where
     Return x -> return x
     NewRef   s   k -> do r <- newIORef s
                          k r
     ReadRef  r   k -> do s <- readIORef r
                          k s
     WriteRef r s k -> do writeIORef r s
                          k ()
 |]

phrase1 :: RefComp Char Char
phrase1 = newRef 'a' >>= readRef

phrase2 :: RefComp Char Char
phrase2 = newRef 'z' >> newRef 'a' >>= readRef

test1 :: IO Char
test1 = iORefState phrase1

test3 :: IO (Char, Int)
test3 = iORefState (countRef phrase1)

test5 :: IO (Char, Int)
test5 = iORefState (countRef phrase2)
