module ParseHandlers where

import Text.ParserCombinators.Parsec
import Data.Char (isSpace)

{- TODO:

  * Generate type signatures for operation functions.

  * Syntax for handler extension?

  * McBride handlers?

  * Closure conversion? Perhaps not feasible using Template Haskell.

-}

{- Examples -}
{-
  State operations:

    [operation|Get s : s|]
    [operation|Put s : s -> ()|]

  These elaborate to:

    data Get s = Get
    type instance Return (Get s) = s
    get = doOp Get

    newtype Put s = Put s
    type instance Return (Put s) = ()
    put s = doOp (Put s)

  If one of the parameters to an operation has a fancy type then it is
  sometimes necessary to add a type annotation on the generated
  operation function. This is perfectly possible. We might improve
  usability by outputting a type-signature (as it should always be
  fully known anyway).

  A non-forwarding state handler:

    [handler|StateHandler s a : {Get s, Put s} -> s -> a where
      clause (StateHandler s) Get k = k (StateHandler s) s
      clause _ (Put s) k = k (StateHandler s) ()
    |]

  This elaborates to:

    newtype StateHandler s a = StateHandler s
    type instance Result (StateHandler s a) = a
    instance (StateHandler s a `Handles` Get s) where
      clause (StateHandler s) Get k = k (StateHandler s) s
    instance (StateHandler s a `Handles` Put s) where
      clause _ (Put s) k = k (StateHandler s) ()

  A forwarding state handler:

    [handler|forward h.FStateHandler s a : {Get s, Put s} -> s -> a where
      clause (FStateHandler s) Get k = k (FStateHandler s) s
      clause _ (Put s) k = k (FStateHandler s) ()
    |]

  This prepends h to the list of FStateHandler's type variables yielding:

    newtype FStateHandler h s a = FStateHandler s
    type instance Result (FStateHandler h s a) = a
    instance (FStateHandler h s a `Handles` Get s) where
      clause (FStateHandler s) Get k = k (FStateHandler s) s
    instance (FStateHandler h s a `Handles` Put s) where
      clause _ (Put s) k = k (FStateHandler s) ()

  and additionally generates the following forwarding instances:

    instance (h `Handles` op) => (PVHandler h a `Handles` op) where
      clause h op k = doOp op >>= k h
    instance (h `PolyHandles` op) => (PVHandler h a `PolyHandles` op) where
      polyClause h op k = polyDoOp op >>= k h

  A polymorphic operation:

    [operation|Failure : forall a.a|]

  This elaborates to:

    data Failure a = Failure
    type instance Return (Failure a) = a
    failure = doPolyOp Failure

  A polymorphic handler:

    [handler|MaybeHandler a : {Failure} -> Maybe a where
       polyClause _ Failure k = Nothing
    |]

  This elaborates to

    newtype MaybeHandler a = MaybeHandler
    type instance Result (MaybeHandler a) = a
    instance (MaybeHandler a `PolyHandles` Failure) where
      polyClause _ Failure k = Nothing

  The collection of operations in the curly braces includes only those
  operations whoses clauses are defined up-front. Further clauses can
  be added later using explicit instances of the Handles type
  class. Sometimes we have to do this when we require an explicit
  class constraint.

-}

{- Handler definitions -}

type HandlerDef = (Maybe String, String, [String], [(String, [String])], String, String)

handlerSig :: GenParser Char a ([(String, [String])], String)
handlerSig =
    do
      sig <-
          (do
            char '{'
            sig <- opSig `sepBy1` char ','
            char '}'
            spaces
            string "->"
            spaces
            return sig)
           <|>
           (return [])
      r <- result
      return (sig, r)

opSig :: GenParser Char a (String, [String])
opSig =
    do
      spaces
      name <- upperId
      spaces
      ts <- tyVars
      return (name, ts)
      

parseHandlerDef :: String -> HandlerDef
parseHandlerDef s =
    case parse handlerdef "" s of
      Right r -> r


handlerdef :: GenParser Char a HandlerDef
handlerdef =
    do
      spaces
      h <- optionMaybe forward
      name <- upperId
      spaces
      ts <- tyVars
      char ':'
      spaces
      (sig, r) <- handlerSig
      cs <- clauses
      return (h, name, ts, sig, r, cs)

forward =
    do
      string "forward"
      spaces
      h <- lowerId
      spaces
      char '.'
      spaces
      return h

isSpaceNoNewline = satisfy (\c -> isSpace c && c /= '\n' && c /= '\r')

result = manyTill anyChar (try (do {spaces; string "where"; many isSpaceNoNewline; many newline}))
clauses = many anyChar


{- Operation definitions -}

parseOpDef :: String -> (String, [String], String)
parseOpDef s =
    case parse opdef "" s of
      Right r -> r

opdef :: GenParser Char a (String, [String], String)
opdef =
    do
      name <- upperId
      spaces
      xs <- tyVars
      char ':'
      spaces
      sig <- many anyChar
      return (name, xs, sig)

{- Utilities -}
      
tyVars :: GenParser Char a [String]
tyVars = many (do {x <- tyVar; spaces; return x})

tyVar :: GenParser Char a String
tyVar = lowerId

lowerId :: GenParser Char a String
lowerId =
  do
    c <- lower
    cs <- many alphaNum
    return (c : cs)

upperId :: GenParser Char a String
upperId =
  do
    c <- upper
    cs <- many alphaNum
    return (c : cs)


