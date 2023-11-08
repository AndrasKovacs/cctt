
module Lexer where

import FlatParse.Stateful
  hiding (Parser, runParser, string, char, cut, Pos, Span, getPos, err)

import qualified FlatParse.Stateful as FP
import qualified Data.ByteString.Char8 as B
import Language.Haskell.TH

import Data.String
import qualified Data.Set as S
import Data.Char

import Common
import Presyntax

----------------------------------------------------------------------------------------------------

data Expected
  = Lit String -- ^ Expected a concrete `String`.
  | Msg String -- ^ An arbitrary error message.
  deriving (Eq, Show, Ord)

instance IsString Expected where fromString = Lit

data Error'
  = Precise Expected     -- ^ Expected exactly something.
  | Imprecise [String]   -- ^ Expected one of multiple things.
  deriving Show

data Error
  = Error {-# unpack #-} Pos Error'
  | DontUnboxError
  deriving Show

merge :: Error -> Error -> Error
merge err@(Error p e) err'@(Error p' e')
  | p == p', Imprecise ss <- e, Imprecise ss' <- e' = err'
  | otherwise = err
merge _ _ = impossible
{-# noinline merge #-}

type Parser = FP.Parser Src Error

prettyError :: Src -> Error -> String
prettyError src DontUnboxError = impossible
prettyError src (Error pos e)  =

  let bstr   = srcToBs src
      ls     = FP.linesUtf8 bstr
      (l, c) = head $ posLineCols bstr [rawPos pos]
      line   = if 0 <= l && l < length ls then ls !! l else ""
      linum  = show (l+1)
      lpad   = map (const ' ') linum

      expected (Lit s) = "expected " ++ s
      expected (Msg s) = s

      err (Precise exp)     = expected exp
      err (Imprecise exps)  = imprec $ S.toList $ S.fromList exps

      imprec :: [String] -> String
      imprec [] = impossible
      imprec [s] = "expected " ++ s
      imprec ss = "expected one of the following:\n" ++ unlines (map ("  - "++) ss)

      showsrc (SrcFile path _) = path
      showsrc SrcImpossible    = impossible

  in "parse error:\n"++
     showsrc src ++ ":" ++ show l ++ ":" ++ show c ++ ":\n" ++
     lpad   ++ "|\n" ++
     linum  ++ "| " ++ line ++ "\n" ++
     lpad   ++ "| " ++ replicate c ' ' ++ "^\n" ++
     err e

getPos :: Parser Pos
getPos = Pos <$> ask <*> FP.getPos
{-# inline getPos #-}

-- | Throw an error.
err :: Error' -> Parser a
err err = do
  pos <- getPos
  FP.err $ Error pos err

-- | Imprecise cut: we slap a list of expected things on inner errors.
cut :: Parser a -> [String] -> Parser a
cut p exps = do
  pos <- getPos
  cutting p (Error pos (Imprecise exps)) merge

-- | Precise cut: we propagate at most a single expected thing.
pcut :: Parser a -> Expected -> Parser a
pcut p exp = do
  pos <- getPos
  cutting p (Error pos (Precise exp)) merge

runParser :: Parser a -> Src -> Result Error a
runParser p src = FP.runParser p src 0 (srcToBs src)

-- | Run parser, print pretty error on failure.
testParser :: Show a => Parser a -> String -> IO ()
testParser p str = case SrcFile "(interactive)" (strToUtf8 str) of
  b -> case runParser p b of
    Err e    -> putStrLn $ prettyError b e
    OK a _ _ -> print a
    Fail     -> putStrLn "parse error"

dummy :: Parser ()
dummy = pure ()
{-# inline dummy #-}

ws :: Parser ()
ws = $(switch [| case _ of
  " "  -> dummy >> ws
  "\n" -> dummy >> ws
  "\t" -> dummy >> ws
  "\r" -> dummy >> ws
  "--" -> dummy >> lineComment
  "{-" -> dummy >> multilineComment
  _    -> pure () |])

-- | Parse a line comment.
lineComment :: Parser ()
lineComment =
  withOption anyWord8
    (\case 10 -> ws
           _  -> lineComment)
    (pure ())

-- | Parse a potentially nested multiline comment.
multilineComment :: Parser ()
multilineComment = go (1 :: Int) where
  go 0 = ws
  go n = $(switch [| case _ of
    "\n" -> dummy >> go n
    "-}" -> dummy >> go (n - 1)
    "{-" -> dummy >> go (n + 1)
    _    -> FP.branch anyChar (go n) (pure ()) |])

token :: Parser a -> Parser a
token p = p <* ws
{-# inline token #-}

spanOfToken :: Parser a -> Parser Span
spanOfToken p = do
  src <- ask
  FP.Span x y <- FP.spanOf p <* ws
  pure $ Span# src x y
{-# inline spanOfToken #-}

-- | Read a starting character of an identifier.
identStartChar :: Parser Char
identStartChar = fusedSatisfy
  isLatinLetter
  (\c -> isGreekLetter c || isLetter c)
  isLetter
  isLetter

-- | Read a non-starting character of an identifier.
identChar :: Parser Char
identChar = fusedSatisfy
  (\c -> isLatinLetter c || FP.isDigit c || c == '\'' || c == '-')
  (\c -> isGreekLetter c || isAlphaNum c)
  isAlphaNum
  isAlphaNum

inlineIdentChar :: Parser Char
inlineIdentChar = fusedSatisfy
  (\c -> isLatinLetter c || FP.isDigit c || c == '\'' || c == '-')
  (\c -> isGreekLetter c || isAlphaNum c)
  isAlphaNum
  isAlphaNum
{-# inline inlineIdentChar #-}

-- | Parse a non-keyword string, return the `Span` of the symbol.
sym :: String -> Q Exp
sym str = [| spanOfToken $(FP.string str) |]

-- | Parse a non-keyword string, throw precise error on failure, return the `Span` of the symbol
sym' :: String -> Q Exp
sym' str =
  [| spanOfToken ($(FP.string str) `pcut` Lit str) |]

-- | Parse a keyword string, return the `Span`.
kw :: String -> Q Exp
kw str =
  [| spanOfToken ($(FP.string str) `notFollowedBy` identChar) |]

-- | Parse a keyword string, throw precise error on failure, return the `Span`.
kw' :: String -> Q Exp
kw' str =
  [| spanOfToken (($(FP.string str) `notFollowedBy` identChar) `pcut` Lit str) |]

-- | Raw non-token parser that reads any keyword.
anyKw :: Parser ()
anyKw = $(switch [| case _ of
  "Glue"      -> eof
  "I"         -> eof
  "U"         -> eof
  "ap"        -> eof
  "case"      -> eof
  "coe"       -> eof
  "com"       -> eof
  "inductive" -> eof
  "higher"    -> eof
  "glue"      -> eof
  "module"    -> eof
  "hcom"      -> eof
  "import"    -> eof
  "let"       -> eof
  "refl"      -> eof
  "unglue"    -> eof
  "λ"         -> eof |])

manyIdentChars :: Parser ()
manyIdentChars = skipMany identChar

scanIdent :: Parser ()
scanIdent = identStartChar >> skipMany inlineIdentChar

withSpan :: Parser a -> Parser (a, Span)
withSpan a = FP.withSpan a \a (FP.Span x y) -> do
  src <- ask
  pure (a, Span# src x y)

identBase :: Parser Presyntax.Name
identBase = FP.withSpan scanIdent \_ span@(FP.Span x y) -> do
  fails $ inSpan span anyKw
  ws
  src <- ask
  pure $ Span# src x y

-- | Parse an identifier.
ident :: Parser Presyntax.Name
ident = identBase
{-# inline ident #-}

-- | Parse an identifier.
ident' :: Parser Presyntax.Name
ident' = identBase `pcut` Lit "identifier"
{-# inline ident' #-}

test = FP.runParser traceRest () 0 (B.pack "")
