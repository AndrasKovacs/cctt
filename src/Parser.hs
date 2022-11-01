
module Parser (parseString, parseStdin) where

import Common
import Presyntax

import Prelude hiding (pi)
import Text.Megaparsec
import Data.Char
import Data.Void
import Data.Foldable
import System.Exit

import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

--------------------------------------------------------------------------------

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser Tm -> Parser Tm
withPos p = do
  pos <- getSourcePos
  p >>= \case
    t@Pos{} -> pure t
    t       -> pure $ Pos (coerce pos) t

lexeme     = L.lexeme ws
symbol s   = lexeme (C.string s)
char c     = lexeme (C.char c)
parens p   = char '(' *> p <* char ')'
arrow      = symbol "→" <|> symbol "->"
bind       = ident <|> symbol "_"
lambda     = char '\\' <|> char 'λ'
p1         = symbol ".1" <|> symbol ".₁"
p2         = symbol ".2" <|> symbol ".₂"
prod       = char '*' <|> char '×'

branch :: Parser a -> (a -> Parser b) -> Parser b -> Parser b
branch p t f = (t =<< p) <|> f

isKeyword :: String -> Bool
isKeyword x =
     x == "let"
  || x == "λ"
  || x == "U"
  || x == "Nat"
  || x == "zero"
  || x == "suc"
  || x == "NatElim"
  || x == "coe"
  || x == "hcom"
  || x == "Glue"
  || x == "glue"
  || x == "unglue"

ident :: Parser Name
ident = try $ do
  o <- getOffset
  x <- takeWhile1P Nothing isAlphaNum
  if isKeyword x
    then do {setOffset o; fail $ "unexpected keyword: " ++ x}
    else x <$ ws

keyword :: String -> Parser ()
keyword kw = do
  C.string kw
  (takeWhile1P Nothing isAlphaNum *> empty) <|> ws

atom :: Parser Tm
atom =
      parens tm
  <|> withPos (    (U     <$  keyword "U"   )
               <|> (Nat   <$  keyword "Nat" )
               <|> (Zero  <$  keyword "zero")
               <|> (I0    <$  keyword  "0"  )
               <|> (I1    <$  keyword  "1"  )
               <|> (Ident <$> ident         ))

goProj :: Tm -> Parser Tm
goProj t =
      (p1 *> goProj (Proj1 t) <|> (p2 *> goProj (Proj2 t)))
  <|> (pure t)

proj :: Parser Tm
proj = goProj =<< atom

intLit :: Parser Tm
intLit = (I0 <$ keyword "0") <|> (I1 <$ keyword "1")

int :: Parser Tm
int = intLit <|> (Ident <$> ident)

cofEq :: Parser CofEq
cofEq = CofEq <$> int <*> (char '=' *> int)

-- TODO: do we even need CTrue anywhere?
cof :: Parser Cof
cof = CAnd <$> cofEq <*> ((char ',' *> cof) <|> pure CTrue)

goSys :: Parser System
goSys =
      (SCons <$> (cof <* arrow) <*> (tm <* char ';') <*> goSys)
  <|> pure SEmpty

sys :: Parser System
sys = char '[' *> goSys <* char ']'

goApp :: Tm -> Parser Tm
goApp t = (goApp =<< (App t <$> proj)) <|> pure t

app :: Parser Tm
app =
       (keyword "suc"     *> (Suc <$> proj))
  <|>  (keyword "NatElim" *> (NatElim <$> proj <*> proj <*> proj <*> proj))
  <|>  (keyword "coe"     *> (Coe <$> int <*> int <*> bind <*> proj <*> proj))
  <|>  (keyword "hcom"    *> (HCom <$> int <*> int <*> bind <*> proj <*> sys <*> proj))
  <|>  (keyword "Glue"    *> (GlueTy <$> proj <*> sys))
  <|>  (keyword "glue"    *> (GlueTm <$> proj))
  <|>  (keyword "unglue"  *> (Unglue <$> proj))
  <|>  (goApp =<< proj)

eq :: Parser Tm
eq = do
  t <- app
  branch (char '=')
    (\_ -> Path t <$> app)
    (pure t)

sigma :: Parser Tm
sigma =
  branch (char '(' *> bind <* char ':')
    (\x -> do
        a <- tm
        char ')'
        prod
        b <- sigma
        pure $ Sg x a b)
    (do t <- eq
        branch prod
          (\_ -> Sg "_" t <$> sigma)
          (pure t))

piBinder :: Parser ([Name], Ty)
piBinder =
  (,) <$> (char '(' *> some bind) <*> (char ':' *> tm <* char ')')

pi :: Parser Tm
pi =
  branch (try (some piBinder))
    (\case
        [([x], a)] -> branch arrow
          (\_ -> Pi x a <$> pi)
          (do prod
              dom <- Sg x a <$> sigma
              branch arrow
                (\_ -> Pi "_" dom <$> pi)
                (pure dom))
        bs -> do
          arrow
          b <- pi
          pure $! foldr' (\(xs, a) t -> foldr' (\x b -> Pi x a b) t xs) b bs)

    (do t <- sigma
        branch arrow
          (\_ -> Pi "_" t <$> pi)
          (pure t))

lam :: Parser Tm
lam = do
  lambda
  bs <- some bind
  char '.'
  t <- lamlet
  pure $! foldr' Lam t bs

pLet :: Parser Tm
pLet = do
  keyword "let"
  x <- ident
  ma <- optional (try (char ':' *> notFollowedBy (char '=')) *> tm)
  symbol ":="
  t <- tm
  char ';'
  u <- lamlet
  pure $ Let x ma t u

lamlet :: Parser Tm
lamlet = lam <|> pLet <|> pi

tm :: Parser Tm
tm = withPos do
  t <- lamlet
  branch (char ',')
    (\_ -> Pair t <$> lamlet)
    (pure t)

top :: Parser Top
top = branch ident
  (\x -> do
    ma <- optional (try (char ':' *> notFollowedBy (char '=')) *> tm)
    symbol ":="
    t <- tm
    char ';'
    u <- top
    pure $ TDef x ma t u)
  (pure TEmpty)

src :: Parser Top
src = ws *> top <* eof

parseString :: String -> IO Top
parseString s =
  case parse src "(stdin)" s of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitFailure
    Right t ->
      pure t

parseStdin :: IO (Top, String)
parseStdin = do
  s <- getContents
  t <- parseString s
  pure (t, s)
