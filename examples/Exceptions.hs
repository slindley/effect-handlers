{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction,
    RankNTypes,
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
  forward h.(h `PolyHandles` DivideByZero, h `Handles` Divide) =>
    CheckZeroHandler a :: a
      handles {Divide} where
        Divide x y k -> if y == 0 then divideByZero
                        else (x `divide` y) >>= k
        Return x     -> return x
|]
[handler|
  forward h.ReportErrorHandler a :: Either String a
    polyhandles {DivideByZero} where
      DivideByZero k -> return $ Left "Cannot divide by zero"
      Return x       -> return (Right x)
|]


type D a   = forall h.(h `Handles` Divide) => Comp h a
type DZ a  = forall h.(h `PolyHandles` DivideByZero) => Comp h a
type DDZ a = forall h.(h `PolyHandles` DivideByZero, h `Handles` Divide) => Comp h a

divUnchecked :: D a -> a
divUnchecked comp = (handlePure . divideHandler) comp 

divChecked :: D a -> Either String a
divChecked comp = (handlePure . reportErrorHandler . divideHandler . checkZeroHandler) comp

