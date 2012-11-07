module ParseHandlers where

import Text.ParserCombinators.Parsec
import Data.Char (isSpace)
import ParseCode

-- we could use the applicative interface...
--
-- I'm not convinced that it makes things clearer though
--
--import Control.Applicative ((<*>), (<*), (*>), (<$>), (<$))

data OpKind = Plain | Poly | Mono
  deriving Show

{- Handler definitions -}
type HandlerDef = (Maybe (String, Maybe String),
                   String,
                   [String],
                   ([(OpKind, [(String, [String])])]),
                   String,
                   String)

handlerSig :: String -> OpKind -> GenParser Char a (OpKind, [(String, [String])])
handlerSig s k =
    do
      sig <-
          (do
            string s
            spaces
            char '{'
            sig <- opSig `sepBy1` char ','
            char '}'
            spaces
            return sig)
      return (k, sig)

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
      string "::"
      spaces
      r <- result
      spaces
      sigs <- (handlerSig "handles" Plain <|> handlerSig "polyhandles" Poly <|> handlerSig "monohandles" Mono) `sepBy` spaces
      spaces
      string "where"
      many isSpaceNoNewline
      many newline
      cs <- clauses
      return (h, name, ts, sigs, r, cs)

forward =
    do
      string "forward"
      spaces
      h <- lowerId
      spaces
      char '.'
      spaces
      c <- optionMaybe handlerConstraint
      return (h, c)

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
                                                  string "polyhandles" <|>
                                                  string "monohandles" <|>
                                                  string "where"})))
--result = manyTill anyChar (try (do {spaces; string "where"; many isSpaceNoNewline; many newline}))
clauses = many anyChar


data QuantifierKind = Forall | Exists
  deriving Show
type OpDef = (Maybe (QuantifierKind, String), String, [String], String)

{- Operation definitions -}

parseOpDef :: String -> OpDef
parseOpDef s =
    case parse opdef "" s of
      Right r -> r

opdef :: GenParser Char a OpDef
opdef =
    do
      spaces
      a <- optionMaybe quantifier
      name <- upperId
      spaces
      xs <- tyVars
      string "::"
      spaces
      sig <- many anyChar
      return (a, name, xs, sig)

quantifierKind :: GenParser Char a QuantifierKind
quantifierKind = do {string "exists"; return Exists} <|> do {string "forall"; return Forall}

quantifier =
    do
      q <- quantifierKind
      spaces
      h <- lowerId
      spaces
      char '.'
      spaces
      return (q, h)

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


