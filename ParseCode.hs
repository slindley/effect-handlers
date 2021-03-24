{-# LANGUAGE FlexibleContexts #-}

module ParseCode (top, paren) where

import Text.ParserCombinators.Parsec

-- Parser for retrieving well-bracketted Haskell code
top :: GenParser Char a String -> GenParser Char a String
top stop =
    do
      ss <- manyTill (try $ chunk stop) (try $ lookAhead $ stop)
      s <- manyTill anyChar (try $ lookAhead stop)
      return $ concat (ss ++ [s])

chunk :: GenParser Char a String -> GenParser Char a String
chunk stop =
    let openers = "([{\"" in
    do
      s <- manyTill (noneOf openers) (try $ (lookAhead (oneOf openers) >> return "") <|> (lookAhead stop))
      s' <- (block <|> do {try $ lookAhead stop; return ""})
      return $ s ++ s'

-- disable single quotes because they can be used in names...
block :: GenParser Char a String
block = paren <|> bracket <|> brace <|> double -- <|> single

paren :: GenParser Char a String
paren = group '(' ')'

bracket :: GenParser Char a String
bracket = group '[' ']'

brace :: GenParser Char a String
brace = group '{' '}'

group :: Char -> Char -> GenParser Char a String
group open close =
    do
      char open
      s <- groupBody
      char close
      return $ [open] ++ s ++ [close]

groupBody :: GenParser Char a String
groupBody =
    let boring = noneOf "()[]{}\"\\" in
    do
      ss <- many $ try $ do {s <- many $ boring; s' <- block; return $ s ++ s'}
      s <- many boring
      return $ concat $ ss ++ [s]

double :: GenParser Char a String
double = quote '"'

-- single :: GenParser Char a String
-- single = quote '\''

quote :: Char -> GenParser Char a String
quote q =
    do
      char q
      s <- quoteBody q
      char q
      return $ [q] ++ s ++ [q]

quoteBody q =
    do
      s <- many (noneOf [q,'\\'])
      (do {lookAhead (char q); return $ s} <|>
       do {char '\\'; c <- anyChar; s' <- quoteBody q; return $ s ++ "\\" ++ [c] ++ s'})
