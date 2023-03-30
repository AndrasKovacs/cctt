
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
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")

withPos :: Parser Tm -> Parser Tm
withPos p = do
  pos <- getSourcePos
  p >>= \case
    t@Pos{} -> pure t
    t       -> pure $ Pos (coerce pos) t

lexeme     = L.lexeme ws
decimal    = lexeme (L.decimal :: Parser Lvl)
symbol s   = lexeme (C.string s)
char c     = lexeme (C.char c)
parens p   = char '(' *> p <* char ')'
arrow      = symbol "→" <|> symbol "->"
bind       = ident <|> symbol "_"
lambda     = char '\\' <|> char 'λ'
prod       = char '*' <|> char '×'

branch :: Parser a -> (a -> Parser b) -> Parser b -> Parser b
branch p t f = (t =<< p) <|> f

-- isKeyword :: String -> Bool
-- isKeyword = \case
--   "Glue"   -> True
--   "I"      -> True
--   "U"      -> True
--   "ap"     -> True
--   "coe"    -> True
--   "com"    -> True
--   "data"   -> True
--   "elim"   -> True
--   "glue"   -> True
--   "hcom"   -> True
--   "import" -> True
--   "let"    -> True
--   "refl"   -> True
--   "unglue" -> True
--   "λ"      -> True
--   _        -> False

isKeyword :: String -> Bool
isKeyword = \case
  'G':'l':'u':'e':[]         -> True
  'I':[]                     -> True
  'U':[]                     -> True
  'a':'p':[]                 -> True
  'c':'o':'e':[]             -> True
  'c':'o':'m':[]             -> True
  'd':'a':'t':'a':[]         -> True
  'e':'l':'i':'m':[]         -> True
  'g':'l':'u':'e':[]         -> True
  'h':'c':'o':'m':[]         -> True
  'i':'m':'p':'o':'r':'t':[] -> True
  'l':'e':'t':[]             -> True
  'r':'e':'f':'l':[]         -> True
  'u':'n':'g':'l':'u':'e':[] -> True
  'λ':[]                     -> True
  _                          -> False


ident :: Parser Name
ident = try do
  o <- getOffset
  x <- takeWhile1P Nothing (\c -> isAlphaNum c || c == '\'')
  if isKeyword x
    then do {setOffset o; fail $ "unexpected keyword: " ++ x}
    else x <$ ws

keyword :: String -> Parser ()
keyword kw = try do
  C.string kw
  (takeWhile1P Nothing (\c -> isAlphaNum c || c == '\'') *> empty) <|> ws

atom :: Parser Tm
atom =
      parens tm
  <|> withPos (    (U     <$  keyword "U"   )
               <|> (I0    <$  keyword  "0"  )
               <|> (I1    <$  keyword  "1"  )
               <|> (I     <$  keyword  "I"  )
               <|> (Refl  <$  keyword "refl")
               <|> (TopLvl   <$!> (C.string "@@" *> decimal))
               <|> (LocalLvl <$!> (C.char '@'    *> decimal))
               <|> (do {p <- getSourcePos; char '?'; id <- optional ident; pure (Hole id (coerce p))})
               <|> (Ident <$!> ident))

goProj :: Tm -> Parser Tm
goProj t =
  branch (char '.')
    (\_ -> (char '1' *> goProj (Proj1 t))
       <|> (char '₁' *> goProj (Proj1 t))
       <|> (char '2' *> goProj (Proj2 t))
       <|> (char '₂' *> goProj (Proj2 t))
       <|> (do {x <- ident; goProj (ProjField t x)}))
    ((symbol "⁻¹" *> goProj (Sym t)) <|> pure t)

proj :: Parser Tm
proj = goProj =<< atom

intLit :: Parser Tm
intLit = (I0 <$ keyword "0") <|> (I1 <$ keyword "1")

int :: Parser Tm
int = intLit
  <|> (ILvl <$!> (C.char '@' *> (coerce decimal)))
  <|> (Ident <$!> ident)

cofEq :: Parser CofEq
cofEq = CofEq <$!> int <*!> (char '=' *> int)

-- TODO: do we even need CTrue anywhere?
cof :: Parser Cof
cof = CAnd <$!> cofEq <*!> ((char ',' *> cof) <|> pure CTrue)

goSys' :: Parser Sys
goSys' =
      (SCons <$!> (char ';' *> cof <* char '.') <*!> tm <*!> goSys')
  <|> pure SEmpty

goSys :: Parser Sys
goSys =
      (SCons <$!> (cof <* char '.') <*!> tm <*!> goSys')
  <|> pure SEmpty

sysBindMaybe :: Parser BindMaybe
sysBindMaybe =
  branch bind
    (\x -> Bind x <$!> (char '.' *> tm))
    (DontBind <$!> (char '.' *> tm))

goSysHCom' :: Parser SysHCom
goSysHCom' =
      (SHCons <$!> (char ';' *> cof) <*!> sysBindMaybe <*!> goSysHCom')
  <|> pure SHEmpty

goSysHCom :: Parser SysHCom
goSysHCom =
      (SHCons <$!> cof <*!> sysBindMaybe <*!> goSysHCom')
  <|> pure SHEmpty

sys :: Parser Sys
sys = char '[' *> goSys <* char ']'

sysHCom :: Parser SysHCom
sysHCom = char '[' *> goSysHCom <* char ']'

goApp :: Tm -> Parser Tm
goApp t =
      do {l <- char '{' *> tm <* char '}'; r <- char '{' *> tm <* char '}'; u <- proj;
          goApp (PApp l r t u)}
  <|> do {u <- proj; goApp (App t u)}
  <|> pure t

bindMaybe :: Parser BindMaybe
bindMaybe = branch (try (char '(' *> bind <* char '.'))
  (\x -> Bind x <$!> (tm <* char ')'))
  (DontBind <$!> proj)

goCoe :: Parser Tm
goCoe = do
  r  <- int
  r' <- int
  a  <- bindMaybe
  t  <- proj
  pure $ Coe r r' a t

goCom :: Parser Tm
goCom = do
  r   <- int
  r'  <- int
  a   <- bindMaybe
  sys <- sysHCom
  t   <- proj
  pure $ Com r r' a sys t

methods :: Parser [([Name], Tm)]
methods =
  char '[' *>
  sepBy ((,) <$!> ((:) <$!> ident <*!> many bind) <*!> (char '.' *> tm)) (char ';')
  <* char ']'

goElim :: Parser Tm
goElim = do
  motive  <- optional proj
  methods <- methods
  arg     <- optional proj
  pure $ Elim motive methods arg

goGlue :: Parser Tm
goGlue = do
  base <- proj
  sys1 <- sys
  sys2 <- optional sys
  case sys2 of
    Nothing   -> pure $ GlueTm base Nothing sys1
    Just sys2 -> pure $ GlueTm base (Just sys1) sys2

app :: Parser Tm
app = withPos (
       (keyword "coe"     *> goCoe)
  <|>  (keyword "hcom"    *> (HCom <$!> int <*!> int <*!> optional proj <*!> sysHCom <*!> proj))
  <|>  (keyword "elim"    *> goElim)
  <|>  (keyword "Glue"    *> (GlueTy <$!> proj <*!> sys))
  <|>  (keyword "glue"    *> goGlue)
  <|>  (keyword "unglue"  *> (Unglue <$!> proj))
  <|>  (keyword "com"     *> goCom)
  <|>  (keyword "ap"      *> (Ap <$!> proj <*!> proj))
  <|>  (goApp =<< proj))

trans :: Parser Tm
trans = foldr1 Trans <$!> sepBy1 app (char '∙')

eq :: Parser Tm
eq = do
  t <- trans
  branch (char '=')
    (\_ -> do
        branch (char '{')
          (\_ -> do
              a <- branch (try (bind <* char '.'))
                     (\x -> Bind x <$!> tm)
                     (DontBind <$!> tm)
              char '}'
              u <- trans
              pure $ DepPath a t u)
          (Path t <$!> trans))
    (pure t)

sigma :: Parser Tm
sigma =
  branch (try (char '(' *> bind <* char ':'))
    (\x -> do
        a <- tm
        char ')'
        branch prod
          (\_ -> do
             b <- sigma
             pure $ Sg x a b)
          (pure (Wrap x a)))
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
          (branch prod
            (\_ -> do
              dom <- Sg x a <$!> sigma
              branch arrow
                (\_ -> Pi "_" dom <$!> pi)
                (pure dom))
            (pure (Wrap x a)))
        bs -> do
          arrow
          b <- pi
          pure $! foldr' (\(xs, a) t -> foldr' (\x b -> Pi x a b) t xs) b bs)

    (do t <- sigma
        branch arrow
          (\_ -> Pi "_" t <$!> pi)
          (pure t))

data LamBind = LBind Name | LPLam Tm Tm Name

lamBind :: Parser LamBind
lamBind =
      do {l <- char '{' *> tm <* char '}'; r <- char '{' *> tm <* char '}';
          x <- bind; pure $ LPLam l r x}
  <|> (LBind <$!> bind)

lam :: Parser Tm
lam = do
  lambda
  bs <- some ((,) <$!> getSourcePos <*!> lamBind)
  char '.'
  t <- lamlet
  pure $! foldr'
    (\(pos,b) t -> case b of
        LBind x     -> Pos (coerce pos) (Lam x t)
        LPLam l r x -> Pos (coerce pos) (PLam l r x t))
    t bs
  -- pure $! foldr' (\(pos, x) t -> Pos (coerce pos) (Lam x t)) t bs

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
  ma <- case args of
    [] -> optional (try (char ':' *> notFollowedBy (char '=')) *> tm)
    _  -> do o <- getOffset
             char ':'
             branch (char '=')
               (\_ -> setOffset o >> fail "Expected a type annotation")
               (Just <$!> tm)
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
    (\_ -> Pair t <$!> tm)
    (pure t)

telescope :: Parser [(Name, Ty)]
telescope = do
  bs <- many piBinder
  pure $! foldr' (\(xs, a) acc -> foldr' (\x acc -> (x, a):acc) acc xs) [] bs

top :: Parser Top
top =
  branch ((,) <$!> getSourcePos <*> (keyword "data" *> ident))
    (\(pos, x) -> do
        params <- telescope
        symbol ":="
        constructors <- sepBy ((,) <$!> ident <*!> telescope) (char '|')
        char ';'
        u <- top
        pure $! TData (coerce pos) x params constructors u
    )
    (branch ((,) <$!> getSourcePos <*!> ident)
      (\(pos, x) -> do
        args <- many piBinder
        ma <- case args of
          [] -> optional (try (char ':' *> notFollowedBy (char '=')) *> tm)
          _  -> do o <- getOffset
                   char ':'
                   branch (char '=')
                     (\_ -> setOffset o >> fail "Expected a type annotation")
                     (Just <$!> tm)
        symbol ":="
        t <- tm
        (t, ma) <- pure $! desugarIdentArgs args ma t
        char ';'
        u <- top
        pure $! TDef (coerce pos) x ma t u)
      (branch ((,) <$!> getSourcePos <*!> (keyword "import" *> ident))
        (\(pos, file) -> do
            char ';'
            u <- top
            pure $ TImport (coerce pos) file u)
        (pure TEmpty)))

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
