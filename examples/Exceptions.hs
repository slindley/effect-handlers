{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction,
    RankNTypes, GADTs,
    MultiParamTypeClasses, TemplateHaskell, QuasiQuotes, FlexibleInstances,
    OverlappingInstances, UndecidableInstances,
    FlexibleContexts, TypeOperators, ScopedTypeVariables #-}

import Control.Monad
import Handlers
import DesugarHandlers

[operation|Divide :: Int -> Int -> Int|]
[operation|forall a.DivideByZero :: a|]
[handler|
  forward h.DivideHandler a :: a
    handles {Divide} where
      Divide x y k -> k (x `div` y)
      Return x     -> return x                                   
|]
[handler|
  forward h handles {DivideByZero, Divide}.
    CheckZeroHandler a :: a
      handles {Divide} where
        Divide x y k -> if y == 0 then divideByZero
                        else (x `divide` y) >>= k
        Return x     -> return x
|]
[handler|
  forward h.ReportErrorHandler a :: Either String a
    handles {DivideByZero} where
      DivideByZero k -> return $ Left "Cannot divide by zero"
      Return x       -> return (Right x)
|]

type D a   = forall h.[handles|h {Divide}|] => Comp h a
type DZ a  = forall h.[handles|h {DivideByZero}|] => Comp h a
type DDZ a = forall h.([handles|h {DivideByZero}|], [handles|h {Divide}|]) => Comp h a

divUnchecked :: D a -> a
divUnchecked comp = (handlePure . divideHandler) comp 

divChecked :: D a -> Either String a
divChecked comp = (handlePure . reportErrorHandler . divideHandler . checkZeroHandler) comp

