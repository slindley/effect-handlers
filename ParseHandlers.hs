module ParseHandlers where

import Text.ParserCombinators.Parsec
import Data.Char (isSpace)

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


