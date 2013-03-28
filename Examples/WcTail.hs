{- Word count and tail examples -}

{-# LANGUAGE TypeFamilies,
    GADTs,
    RankNTypes,
    MultiParamTypeClasses,
    QuasiQuotes,
    FlexibleInstances,
    FlexibleContexts,
    OverlappingInstances,
    UndecidableInstances,
    ConstraintKinds,
    DataKinds, 
    NoMonomorphismRestriction   
 #-}

--module Examples.Wc where

import Handlers
import TopLevel
import DesugarHandlers
import System.IO
import Control.Monad
import Network
import Control.Concurrent
import Data.Array.IO

[operation|ReadChar :: Maybe Char|]
[operation|Finished :: Bool|]

readLine :: [handles|h {ReadChar}|] => Comp h String
readLine = 
  do
    mc <- readChar  
    case mc of 
      Nothing   -> return []
      Just '\n' -> return []
      Just c -> do cs <- readLine
                   return (c : cs)
              
-- read from a string
[handler|
  forward h.
    StringReader a :: String -> a
      handles {ReadChar, Finished} where
        Return x   _        -> return x
        ReadChar k []       -> k Nothing []
        ReadChar k (c : cs) -> k (Just c) cs
        Finished k []       -> k True []
        Finished k cs       -> k False cs |]

-- read from stdin
[handler| 
  forward h handles {Io}.
    StdinReader a :: a
      handles {ReadChar, Finished} where
        Return x   -> return x
        ReadChar k -> 
          do
            b <- io (hIsEOF stdin)
            if b then k Nothing else do c <- io getChar; k (Just c)
        Finished k -> do b <- io (hIsEOF stdin); k b|]


{- word count -}
[handler|
  forward h handles {ReadChar}.
    CountChar0 a :: Int -> (a, Int)
      handles {ReadChar} where
        Return x i   -> return (x,i)
        ReadChar k i -> do 
                          m <- readChar
                          case m of
                            Nothing -> k m i
                            Just _  -> k m $! i + 1 |]
countChar = countChar0 0

-- Bool represents whether in a word
[handler|
  forward h handles {ReadChar}.
    CountWord0 a :: Int -> Bool -> (a,Int) 
      handles {ReadChar} where
        Return x   i _ -> return (x,i)
        ReadChar k i b -> 
          do
            m <- readChar
            case m of 
              Nothing -> (k m $! (if b then i + 1 else i)) $ False
              Just c  -> if (c == ' ' || c == '\t' || c == '\n' || c == '\r') then 
                           (k m $! (if b then i + 1 else i)) $ False
                         else
                           k m i True |]
countWord = countWord0 0 False

-- abstract word-count computation
wc :: ([handles|h {ReadChar}|], [handles|h {Finished}|]) => Comp h (Int, Int, Int)
wc = 
   do 
     ((lines, words), chars) <- countChar (countWord (loop 0))   
     return (chars, words, lines)
   where 
   loop i =   
     do
       b <- finished
       if b then return i
       else 
         do
           _ <- readLine  
           loop $! (i + 1)     
          
wcStdin :: IO ()
wcStdin = do            
  (c, w, l) <- handleIO (stdinReader wc)
  putStrLn $ (show l) ++ " " ++ (show w) ++ " " ++ (show c)
              
wcString :: String -> IO ()
wcString s = do            
  (c, w, l) <- handleIO (stringReader s wc)
  putStrLn $ (show l) ++ " " ++ (show w) ++ " " ++ (show c)


{-- Tail --}
[operation|SaveLine :: String -> ()|]
[operation|PrintAll :: ()|]

[handler|
  forward h handles {Io}. 
    KeepAll0 a :: [String] -> Int -> a
      handles {SaveLine, PrintAll} where
        Return x      _  _ -> return x
        SaveLine s k  ss i -> k () (s:ss) i
        PrintAll   k  ss i -> 
          do
            io (forM_ (take i ss) putStrLn) 
            k () ss i |]
keepAll = keepAll0 []

tailComp :: ([handles|h {ReadChar}|], [handles|h {Finished}|],
             [handles|h {SaveLine}|], [handles|h {PrintAll}|]) => Comp h ()
tailComp =
  do
    s <- readLine; saveLine s
    b <- finished; if b then printAll else tailComp
  
data CircularArray = CircularArray !Int !(IOArray Int String) !Int !Int

newCircularArray :: [handles|h {Io}|] => Int -> Comp h CircularArray
newCircularArray n = do
  a <- io (newArray (0, n - 1) []) 
  return (CircularArray n a 0 0)

push :: [handles|h {Io}|] => CircularArray -> String -> Comp h CircularArray
push (CircularArray length arr first next) s =                        
  do
    io (writeArray arr next s)
    let j = incrIdx length next 
    return (CircularArray length arr (if (j == first) then (incrIdx length first) else first) j)

incrIdx :: Int -> Int -> Int
incrIdx length i =
  let j = i + 1 in
  if (j < length) then j else 0

printAllCircularArray :: [handles|h {Io}|] => CircularArray -> Comp h ()
printAllCircularArray (CircularArray length arr first next) = 
    loop first
    where
      loop i = if (i == next) then return () 
               else do 
                      io ((readArray arr i) >>= putStrLn)
                      loop (incrIdx length i)

[handler|  
  forward h handles {Io}.
    LastN0 a :: CircularArray -> a 
      handles {SaveLine, PrintAll} where
        Return x     _ -> return x    
        SaveLine s k c -> push c s >>= k ()
        PrintAll   k c -> printAllCircularArray c >> k () c |]
lastN n comp = do
  c <- newCircularArray n
  lastN0 c comp

tailLastN :: Int -> IO ()
tailLastN n = handleIO (stdinReader (lastN (n+1) tailComp))

tailAll :: Int -> IO ()
tailAll n = handleIO (stdinReader (keepAll n tailComp))

main = tailLastN 20
