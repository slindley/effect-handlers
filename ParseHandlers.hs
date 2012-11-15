module ParseHandlers where

import Text.ParserCombinators.Parsec
import Data.Char (isSpace)
import ParseCode

-- we could use the applicative interface...
--
-- I'm not convinced that it makes things clearer though
--
--import Control.Applicative ((<*>), (<*), (*>), (<$>), (<$))

{- Handles constraints -}

type HandlesConstraint = (String, [(String, [String])])

data QuantifierKind = Forall | Exists
  deriving Show
type OpDef = ([String], String, [String], String)

type HandlerDef = (Maybe (String, [(String, [String])], Maybe String),
                   String,
                   [String],
                   [(String, [String])],
                   String,
                   String)


parseHandlesConstraint :: String -> HandlesConstraint
parseHandlesConstraint s =
    case parse handlesconstraint "" s of
      Right r -> r

handlesconstraint :: GenParser Char a HandlesConstraint
handlesconstraint =
    do
      spaces
      h <- lowerId
      spaces
      sig <- opSigs
      return (h, sig)

{- Handler definitions -}
parseHandlerDef :: String -> HandlerDef
parseHandlerDef s =
    case parse handlerdef "" s of
      Right r -> r


opSigs :: GenParser Char a [(String, [String])]
opSigs = 
    do
      char '{'
      sig <- opSig `sepBy1` char ','
      char '}'
      return sig

handlerSig :: GenParser Char a [(String, [String])]
handlerSig =
    do
      sig <-
          (do
            string "handles"
            spaces
            sig <- opSigs
            spaces
            return sig)
      return sig

opSig :: GenParser Char a (String, [String])
opSig =
    do
      spaces
      name <- upperId
      spaces
      ts <- tyVars
      return (name, ts)

handlerdef :: GenParser Char a HandlerDef
handlerdef =
    do
      spaces
      h <- optionMaybe forward
      name <- upperId
      spaces
      ts <- tyVars
      string "::"
      spaces
      r <- result
      spaces
      sig <- handlerSig
      spaces
      string "where"
      many isSpaceNoNewline
      many newline
      cs <- clauses
      return (h, name, ts, sig, r, cs)

forward =
    do
      string "forward"
      spaces
      h <- lowerId
      spaces
      sig <- option [] handlerSig 
      char '.'
      spaces
      c <- optionMaybe handlerConstraint
      return (h, sig, c)

handlerConstraint :: GenParser Char a String
handlerConstraint =
  do
    c <- paren
    spaces
    string "=>"
    spaces
    return c

isSpaceNoNewline = satisfy (\c -> isSpace c && c /= '\n' && c /= '\r')

result = manyTill anyChar (try (lookAhead
                                (do {many1 space; string "handles" <|>
                                                  string "where"})))
--result = manyTill anyChar (try (do {spaces; string "where"; many isSpaceNoNewline; many newline}))
clauses = many anyChar

{- Operation definitions -}

parseOpDef :: String -> OpDef
parseOpDef s =
    case parse opdef "" s of
      Right r -> r

opdef :: GenParser Char a OpDef
opdef =
    do
      spaces
      us <- option [] forall
      name <- upperId
      spaces
      xs <- tyVars
      string "::"
      spaces
      sig <- many anyChar
      return (us, name, xs, sig)

forall =
    do
      string "forall"
      spaces
      us <- lowerId `sepBy` spaces
      spaces
      char '.'
      spaces
      return us

{- Utilities -}
      
tyVars :: GenParser Char a [String]
tyVars = many (do {x <- tyVar; spaces; return x})

tyVar :: GenParser Char a String
tyVar = lowerId

lowerId :: GenParser Char a String
lowerId =
  do
    c <- lower
    cs <- many (alphaNum <|> char '\'')
    return (c : cs)

upperId :: GenParser Char a String
upperId =
  do
    c <- upper
    cs <- many (alphaNum <|> char '\'')
    return (c : cs)


