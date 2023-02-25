
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
  || x == "com"
  || x == "I"

ident :: Parser Name
ident = try $ do
  o <- getOffset
  x <- takeWhile1P Nothing (\c -> isAlphaNum c || c == '\'')
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
               <|> (I     <$  keyword  "I"  )
               <|> (Ident <$!> ident        ))

goProj :: Tm -> Parser Tm
goProj t =
      (p1 *> goProj (Proj1 t) <|> (p2 *> goProj (Proj2 t)))
  <|> (pure t)

proj :: Parser Tm
proj = goProj =<< atom

intLit :: Parser Tm
intLit = (I0 <$ keyword "0") <|> (I1 <$ keyword "1")

int :: Parser Tm
int = intLit <|> (Ident <$!> ident)

cofEq :: Parser CofEq
cofEq = CofEq <$!> int <*!> (char '=' *> int)

-- TODO: do we even need CTrue anywhere?
cof :: Parser Cof
cof = CAnd <$!> cofEq <*!> ((char ',' *> cof) <|> pure CTrue)

goSys' :: Parser Sys
goSys' =
      (SCons <$!> (char ';' *> cof <* char '.') <*!> tm <*!> goSys)
  <|> pure SEmpty

goSys :: Parser Sys
goSys =
      (SCons <$!> (cof <* char '.') <*!> tm <*!> goSys')
  <|> pure SEmpty

goSysHCom' :: Parser SysHCom
goSysHCom' =
      (SHCons <$!> (char ';' *> cof) <*!> (bind <* char '.') <*!> tm <*!> goSysHCom')
  <|> pure SHEmpty

goSysHCom :: Parser SysHCom
goSysHCom =
      (SHCons <$!> cof <*!> (bind <* char '.') <*!> tm <*!> goSysHCom')
  <|> pure SHEmpty

sys :: Parser Sys
sys = char '[' *> goSys <* char ']'

sysHCom :: Parser SysHCom
sysHCom = char '[' *> goSysHCom <* char ']'

goApp :: Tm -> Parser Tm
goApp t = (goApp =<< (App t <$!> proj)) <|> pure t

-- TODO: sugar for omitting binders, e.g. coe 0 1 p a --> coe 0 1 (i.p i) a
--                                        hcom 0 1 [i=0 k. p k] b --> hcom 0 1 [i=0. p] b
goCoe :: Parser Tm
goCoe = do
  r  <- int
  r' <- int
  char '('
  x <- bind
  char '.'
  a <- tm
  char ')'
  t <- proj
  pure $ Coe r r' x a t

goCom :: Parser Tm
goCom = do
  r  <- int
  r' <- int
  char '('
  x <- bind
  char '.'
  a <- tm
  char ')'
  sys <- sysHCom
  t <- proj
  pure $ Com r r' x a sys t

app :: Parser Tm
app =
       (keyword "suc"     *> (Suc <$!> proj))
  <|>  (keyword "NatElim" *> (NatElim <$!> proj <*!> proj <*!> proj <*!> proj))
  <|>  (keyword "coe"     *> goCoe)
  <|>  (keyword "hcom"    *> (HCom <$!> int <*!> int <*!> optional proj <*!> sysHCom <*!> proj))
  <|>  (keyword "Glue"    *> (GlueTy <$!> proj <*!> sys))
  <|>  (keyword "glue"    *> (GlueTm <$!> proj <*!> sys))
  <|>  (keyword "unglue"  *> (Unglue <$!> proj))
  <|>  (keyword "com"     *> goCom)
  <|>  (goApp =<< proj)

eq :: Parser Tm
eq = do
  t <- app
  branch (char '=')
    (\_ -> do
        branch (char '{')
          (\_ -> branch (try (bind <* char '.'))
            (\x -> do
                a <- tm
                char '}'
                u <- app
                pure (PathP x a t u))
            (do a <- tm
                char '}'
                u <- app
                pure (Path (Just a) t u)))
          (Path Nothing t <$!> app))
    (pure t)

sigma :: Parser Tm
sigma =
  branch (try (char '(' *> bind <* char ':'))
    (\x -> do
        a <- tm
        char ')'
        prod
        b <- sigma
        pure $ Sg x a b)
    (do t <- eq
        branch prod
          (\_ -> Sg "_" t <$!> sigma)
          (pure t))

piBinder :: Parser ([Name], Ty)
piBinder =
  (,) <$!> (char '(' *> some bind) <*!> (char ':' *> tm <* char ')')

pi :: Parser Tm
pi =
  branch (try (some piBinder))
    (\case
        [([x], a)] -> branch arrow
          (\_ -> Pi x a <$!> pi)
          (do prod
              dom <- Sg x a <$!> sigma
              branch arrow
                (\_ -> Pi "_" dom <$!> pi)
                (pure dom))
        bs -> do
          arrow
          b <- pi
          pure $! foldr' (\(xs, a) t -> foldr' (\x b -> Pi x a b) t xs) b bs)

    (do t <- sigma
        branch arrow
          (\_ -> Pi "_" t <$!> pi)
          (pure t))

lam :: Parser Tm
lam = do
  lambda
  bs <- some ((,) <$!> getSourcePos <*!> bind)
  char '.'
  t <- lamlet
  pure $! foldr' (\(pos, x) t -> Pos (coerce pos) (Lam x t)) t bs

-- | Desugar Coq-style definition args.
desugarIdentArgs :: [([Name], Ty)] -> Maybe Ty -> Tm -> (Tm, Maybe Ty)
desugarIdentArgs args mty rhs = (tm, ty) where

  mkTy :: [([Name], Ty)] -> Ty -> Ty
  mkTy args a = foldr' (\(xs, a) b -> foldr' (\x -> Pi x a) b xs) a args

  mkTm :: [([Name], Ty)] -> Tm -> Tm
  mkTm args t = foldr' (\(xs, _) t -> foldr' Lam t xs) t args

  ty = fmap (mkTy args) mty
  tm = mkTm args rhs

pLet :: Parser Tm
pLet = do
  keyword "let"
  x <- ident
  args <- many piBinder
  ma <- optional (try (char ':' *> notFollowedBy (char '=')) *> tm)
  symbol ":="
  t <- tm
  (t, ma) <- pure $! desugarIdentArgs args ma t
  char ';'
  u <- lamlet
  pure $ Let x ma t u

lamlet :: Parser Tm
lamlet = lam <|> pLet <|> pi

tm :: Parser Tm
tm = withPos do
  t <- lamlet
  branch (char ',')
    (\_ -> Pair t <$!> lamlet)
    (pure t)

top :: Parser Top
top = branch ((,) <$!> getSourcePos <*!> ident)
  (\(pos, x) -> do
    args <- many piBinder
    ma <- optional (try (char ':' *> notFollowedBy (char '=')) *> tm)
    symbol ":="
    t <- tm
    (t, ma) <- pure $! desugarIdentArgs args ma t
    char ';'
    u <- top
    pure $ TDef (coerce pos) x ma t u)
  (pure TEmpty)

src :: Parser Top
src = ws *> top <* eof

parseString :: FilePath -> String -> IO Top
parseString path s =
  case parse src path s of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitFailure
    Right t ->
      pure t

parseStdin :: IO (Top, String)
parseStdin = do
  s <- getContents
  t <- parseString "(stdin)" s
  pure (t, s)
