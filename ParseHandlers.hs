module ParseHandlers where

import Text.ParserCombinators.Parsec
import Data.Char (isSpace)
import ParseCode

{- Handler definitions -}

type HandlerDef = (Maybe (String, Maybe String), String, [String], [(String, [String])], String, String)

handlerSig :: GenParser Char a [(String, [String])]
handlerSig =
    do
      spaces
      sig <-
          (do
            string "handles"
            spaces
            char '{'
            sig <- opSig `sepBy1` char ','
            char '}'
            spaces
            return sig)
           <|>
           (return [])
      return sig

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
      r <- result
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

result = manyTill anyChar (try (lookAhead (do {many1 space; string "handles" <|> string "where"})))
--result = manyTill anyChar (try (do {spaces; string "where"; many isSpaceNoNewline; many newline}))
clauses = many anyChar


type OpDef = (Maybe String, String, [String], String)

{- Operation definitions -}

parseOpDef :: String -> OpDef
parseOpDef s =
    case parse opdef "" s of
      Right r -> r

opdef :: GenParser Char a OpDef
opdef =
    do
      spaces
      a <- optionMaybe forall
      name <- upperId
      spaces
      xs <- tyVars
      char ':'
      spaces
      sig <- many anyChar
      return (a, name, xs, sig)

forall =
    do
      string "forall"
      spaces
      h <- lowerId
      spaces
      char '.'
      spaces
      return h


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


