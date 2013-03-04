-- The subtraction game (a variant of the game of nim).
--
-- A game begins with n sticks on the table. A game is played between
-- Alice and Bob. Alice goes first. Alice takes between one and three
-- sticks, then it is Bob's turn, and Bob takes between one and three
-- sticks. They alternate turns until they run out of sticks. The
-- winner is the player who takes the last stick.

{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction, GADTs,
             FlexibleContexts, TypeOperators, UndecidableInstances,
             FlexibleInstances, MultiParamTypeClasses, OverlappingInstances,
             QuasiQuotes
  #-}

import Data.List
import Handlers
import TopLevel
import DesugarHandlers

-- Operations:
--
--   choose (player, n) = m, if player chooses m out of the remaining n sticks

data Player = Alice | Bob
  deriving (Show, Eq)

-- The 'Move' operation represents a move by a player in the game. The
-- parameter is a pair of the player and the number of sticks
-- remaining. The return value is the number of sticks the player
-- chooses to take.
[operation|Move :: Player -> Int -> Int|]

-- We model the rules of the game as an abstract computation over the
-- Move operation returning the winner.

-- a game parameterised by the number of starting sticks
game :: [handles|h {Move}|] => Int -> Comp h Player
game = aliceTurn

aliceTurn n =
  if n == 0 then return Bob
  else
    do
      take <- move Alice n
      bobTurn (n-take)
      
bobTurn n =
  if n == 0 then return Alice
  else
    do
      take <- move Bob n
      aliceTurn (n-take)

-- Note that this implementation does not check that each player takes
-- between one and three sticks on each turn. We will add such a check
-- later.

-- a perfect strategy given n remaining sticks (represented as an
-- operation clause)
perfect :: Int -> (Int -> r) -> r
perfect n k = k (max (n `mod` 4) 1)

-- perfect vs perfect
[handler|
  PP :: Player handles {Move} where
    Return x   -> x
    Move _ n k -> perfect n k
|]
pp :: Int -> Player
pp n = pP (game n)

-- *Main> pp 3
-- Alice
-- *Main> pp 29
-- Alice
-- *Main> pp 32
-- Bob

-- list of valid moves given n sticks remaining
validMoves :: Int -> [Int]
validMoves n = filter (<= n) [1,2,3]

-- a brute force strategy
--
-- Enumerate all the moves. If one of them leads to a win for player,
-- then take it. Otherwise just take 1 stick.
bruteForce :: Player -> Int -> (Int -> Player) -> Player
bruteForce player n k =
  let winners = map k (validMoves n) in
  case (elemIndex player winners) of
    Nothing -> k 1
    Just i  -> k (i+1)

-- brute force vs perfect
[handler|
  BP :: Player handles {Move} where
    Return x        -> x
    Move Alice  n k -> bruteForce Alice n k
    Move Bob    n k -> perfect n k
|]
bp :: Int -> Player
bp n = bP (game n)

-- bruteForce behaves just the same as the perfect strategy, except it
-- is much slower

-- *Main> bp 3
-- Alice
-- *Main> bp 31
-- Alice
-- *Main> bp 32
-- Bob

-- Instead of simply evaluating the winner according to some strategy,
-- we can also compute other data. For instance, we can compute a tree
-- representing the possible moves of each player.

-- a tree encoding possible moves
data MoveTree = Take (Player, [(Int, MoveTree)]) | Winner Player
  deriving Show

-- reify a move as part of a move tree
reifyMove :: Player -> Int -> (Int -> Comp h MoveTree) -> Comp h MoveTree
reifyMove player n k =
  do
    l <- mapM k (validMoves n)
    return $ Take (player, zip [1..] l)
    
-- generate the complete move tree for a game starting with n sticks
[handler|
  MM h :: Comp h MoveTree handles {Move} where
    Return x        -> return (Winner x)
    Move player n k -> reifyMove player n k
|] 
mm :: Int -> MoveTree
mm n = handlePure (mM (game n))
    
-- *Main> mm 3
-- Take (Alice, [(1, Take (Bob, [(1, Take (Alice, [(1,Winner Alice)])),
--                            (2, Winner Bob)])),
--              (2, Take (Bob, [(1,Winner Bob)])),
--              (3, Winner Alice)])

-- generate the move tree for a game in which Bob plays a perfect
-- strategy
[handler|
  forward h handles {Move}.
    MPIn :: MoveTree handles {Move} where
      Return x        -> return (Winner x)
      Move Alice n k -> reifyMove Alice n k
      Move Bob n k   -> do
                          take <- move Bob n
                          tree <- k take
                          return $ Take (Bob, [(take, tree)])
|]
[handler|
  MP :: MoveTree handles {Move} where
    Return x     -> x
    Move Bob n k -> perfect n k
|]
mp :: Int -> MoveTree
mp n = (mP . mPIn) (game n)

-- *Main> mp 3
-- Take (Alice, [(1, Take (Bob, [(2, Winner Bob)])),
--               (2, Take (Bob, [(1, Winner Bob)])),
--               (3, Winner Alice)])
   
-- cheat (p, m) is invoked when player p cheats by attempting to take
-- m sticks (for m < 1 or 3 < m)
[operation|forall a.Cheat :: Player -> Int -> a|]

-- a checked choice
--
-- If the player chooses a valid number of sticks, then the game
-- continues. If not, then the cheat operation is invoked.
checkChoice :: ([handles|h {Move}|], [handles|h {Cheat}|]) =>
               Player -> Int -> (Int -> Comp h a) -> Comp h a
checkChoice player n k =
  do
    take <- move player n
    if take < 0 || 3 < take then cheat player take
    else k take

-- a game that checks for cheating
[handler|
  forward h handles {Move, Cheat}.
    Check :: Player handles {Move} where
      Return x        -> return x
      Move player n k -> checkChoice player n k
|]
checkedGame :: ([handles|h {Move}|], [handles|h {Cheat}|]) => Int -> Comp h Player  
checkedGame n = check (game n)

-- a cheating strategy: take all of the sticks, no matter how many
-- remain
cheater n k = k n

-- Alice cheats against Bob's perfect strategy
-- (Alice always wins)
[handler|
  CP :: Player handles {Move} where
    Return x     -> x
    Move Alice  n k -> cheater n k
    Move Bob    n k -> perfect n k
|]
cp :: Int -> Player
cp n = cP (game n)

-- *Main> cp 32
-- Alice

-- a game in which cheating leads to the game being abandoned, and the
-- cheater is reported along with how many sticks they attempted to
-- take
[handler|
  forward h.CheatEnd :: Player handles {Cheat} where
    Return x         -> return x
    Cheat player n k -> error ("Cheater: " ++ show player ++ ", took; " ++ show n)
|]
cheaterEndingGame :: ([handles|h {Move}|]) => Int -> Comp h Player
cheaterEndingGame n = cheatEnd (checkedGame n)

-- a game in which if Alice cheats then Bob wins immediately, and if Bob
-- cheats then Alice wins immediately
[handler|
  forward h.CheatLose :: Player handles {Cheat} where
    Return x        -> return x
    Cheat Alice n k -> return Bob
    Cheat Bob n k   -> return Alice   
|]
cheaterLosingGame :: ([handles|h {Move}|]) => Int -> Comp h Player
cheaterLosingGame n = cheatLose (checkedGame n)

-- Alice cheats against Bob's perfect strategy
--
-- (If n < 4 then Alice win, otherwise the game is abandoned because
-- Alices cheats.)
cpEnding :: Int -> Player
cpEnding n = cP (cheaterEndingGame n)

-- *Main> cpEnding 3
-- Alice
-- *Main> cpEnding 5
-- *** Exception: Cheater: Alice, took: 5

-- Alice cheat against Bob's perfect strategy
--
-- (If n < 4 then Alice wins, otherwise Bob wins because Alice
-- cheats.)
cpLosing :: Int -> Player
cpLosing n = cP (cheaterLosingGame n)

-- *Main> cpLosing 3
-- Alice
-- *Main> cpLosing 5
-- Bob
