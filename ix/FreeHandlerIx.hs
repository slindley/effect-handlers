{- Handler for indexed types using a free monad -}

{-# LANGUAGE
    GADTs,
    TypeFamilies,
    MultiParamTypeClasses,
    FlexibleInstances,
    FlexibleContexts,
    TypeOperators, 
    PolyKinds, DataKinds, RankNTypes, ScopedTypeVariables
  #-}

module FreeHandlerIx where

import Control.Exception (catch, IOException)
import System.IO

import FunctorIx
import MonadIx

type family Return (op :: k -> *) :: k -> *
type family Result (h ::  k -> *) :: k -> *

class (((h :: k -> *) `Handles` (op :: k -> *))) where
  clause :: op pre -> (forall i.Return op i -> h i -> Result h i) -> h pre -> Result h pre

data Comp (h :: k -> *) (a :: (k -> *)) :: (k -> *) where
  Ret :: a pre -> Comp h a pre
  Do  :: (h `Handles` op) => op pre -> (Return op :-> Comp h a) -> Comp h a pre

instance MonadIx (Comp h) where
  returnIx             = Ret
  extendIx f (Ret v)   = f v
  extendIx f (Do op k) = Do op (\x -> k x ?>= f)
instance FunctorIx (Comp h) where
  mapIx f c = c ?>= (returnIx . f)
instance ApplicativeP (Comp h) where
  pure      = returnP
  mf |*| ms = mf =>= \f -> ms =>= \s -> returnP (f s)

doOp :: (h `Handles` op) => op post -> Comp h (Return op) post
doOp op = Do op returnIx

handle :: Comp h a pre -> (forall i.(a i -> h i -> Result h i)) -> h pre -> Result h pre
handle (Ret x) r h   = r x h
handle (Do op k) r h = clause op (\v h' -> handle (k v) r h') h

-- Example from Kleisli arrows of outrageous fortune
data FileState :: * where
  Open   :: FileState
  Closed :: FileState

data SFileState :: FileState -> * where
  SOpen   :: SFileState 'Open
  SClosed :: SFileState 'Closed

data FOpen i = FOpen ((FilePath := Closed) i)
type instance Return FOpen = SFileState
fOpen :: (h `Handles` FOpen) => String -> Comp h SFileState 'Closed
fOpen p = doOp (FOpen (V p))

data FGetC i = FGetC ((() := 'Open) i)
type instance Return FGetC = Maybe Char := 'Open
fGetC :: (h `Handles` FGetC) => Comp h (Maybe Char := 'Open) 'Open
fGetC = doOp (FGetC (V ()))

data FClose i = FClose ((() := 'Open) i)
type instance Return FClose = () := 'Closed
fClose :: (h `Handles` FClose) => Comp h (() := 'Closed) 'Open
fClose = doOp (FClose (V ()))

fileContents :: (h `Handles` FOpen, h `Handles` FGetC, h `Handles` FClose) =>
                  String -> Comp h (Maybe String := 'Closed) 'Closed
fileContents p = fOpen p ?>= \b -> case b of
  SClosed -> pure Nothing
  SOpen   -> pure (\s _ -> Just s) |*| readOpenFile |*| fClose

readOpenFile :: (h `Handles` FGetC) => Comp h (String := 'Open) 'Open
readOpenFile = fGetC =>= \x -> case x of
  Nothing -> pure ""
  Just c  -> pure (c:) |*| readOpenFile

newtype Wrap (a :: *) (i :: k) = Wrap {unWrap :: a}

data FH (a :: *) (pre :: k) where
     ClosedFH ::           FH a 'Closed 
     OpenFH   :: Handle -> FH a 'Open
type instance Result (FH a) = Wrap (IO a)
                               
instance (FH a `Handles` FOpen) where
  clause (FOpen (V s)) k ClosedFH =
          Wrap
          (catch
           (openFile s ReadMode >>= \h -> unWrap (k SOpen (OpenFH h)))
           (\(_ :: IOException) -> unWrap (k SClosed ClosedFH)))
runFH :: Comp (FH a) (a := 'Closed) 'Closed -> Wrap (IO a) 'Closed
runFH m = handle m (\(V x) _ -> Wrap (return x)) ClosedFH

instance (FH a `Handles` FClose) where
  clause (FClose (V ())) k (OpenFH file) = Wrap (hClose file >> unWrap (k (V ()) ClosedFH))
instance (FH a `Handles` FGetC) where
  clause (FGetC (V ())) k (OpenFH file) =
          Wrap
            (catch
              (hGetChar file >>= \c -> unWrap (k (V (Just c)) (OpenFH file)))
              (\(_ :: IOException) -> unWrap (k (V Nothing) (OpenFH file))))

test1 = unWrap (runFH (fileContents "test.txt"))
test2 = unWrap (runFH (fileContents "HandlerIx.hs"))
