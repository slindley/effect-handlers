> {-# LANGUAGE NoMonomorphismRestriction #-}

> module MRI_code.Advice where

> import Data.Map
> import Control.Monad.State
> import Control.Monad.Identity
> import Control.Monad.Writer
> import Control.Applicative hiding (empty)


BASIC ADVICE CODE

> type Open s = s -> s
>
> new :: Open s -> s
> new a = let this = a this in this
>
> zero :: Open s
> zero = id
> 
> (<@>) :: Open s -> Open s -> Open s
> a1 <@> a2  = \super -> a1 (a2 super)


EXAMPLES

> fib1 :: Open (Int -> Int) 
> fib1 this n = case n of  0 -> 0
>                          1 -> 1
>                          _ -> this (n-1) + this (n-2)

> fib2 :: Open (Int -> Int)
> fib2 super n = case n of  10  -> 55
>                           30  -> 832040
>                           _   -> super n

> slowfib1, slowfib2 :: Int -> Int
> slowfib1  = new fib1
> slowfib2  = new (fib2 <@> fib1)


ALTERNATIVE REPRESENTATION

> type Extension s t c  = s -> t -> c
> type Base s t      = t -> s
> 
> new' :: Base s t -> Extension s t t -> t
> new' base a =  let  this = a (base this) this
>                  in   this
>
> zero' :: Extension s t s
> zero' = \super this -> super 
>
> (<@@@>) :: Extension u t c -> Extension s t u -> Extension s t c
> a1 <@@@> a2 = \super this -> a1 (a2 super this) this

