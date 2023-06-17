
module Parser (parseString, parseByteString, parseStdin) where

import Prelude hiding (pi)

import Data.Char
import Data.Foldable
import System.Exit

import FlatParse.Stateful
  hiding (Parser, runParser, string, char, cut, err,
          Pos, getPos, Span, spanOf, branch, withSpan)

import qualified FlatParse.Stateful as FP
import qualified Data.ByteString.Char8 as B


import Common
import Presyntax
import Lexer

--------------------------------------------------------------------------------

atomErr   = ["identifier", "parenthesized expression", "refl", "interval constant", "hole"]
projErr   = "projection expression" : atomErr
appErr    = "application expression" : projErr
-- pathErr   = "a path type" : appErr
-- sigmaErr  = "a sigma type" : pathErr
-- piErr     = "a function type" : sigmaErr
-- lamLetErr = "a let-definition" : "a lambda expression" : piErr
-- tmErr     = ["a term"] :: [String]

--------------------------------------------------------------------------------

assign'   = $(sym' ":=")
colon     = token  ($(FP.string ":") `notFollowedBy` $(FP.string "="))
colon'    = token' ($(FP.string ":") `notFollowedBy` $(FP.string "="))
semi      = $(sym  ";")
semi'     = $(sym' ";")
comma     = $(sym  ",")
braceL    = $(sym  "{")
braceL'   = $(sym' "{")
parL      = $(sym  "(")
parR'     = $(sym' ")")
dot       = $(sym  ".")
dot'      = $(sym'  ".")
arrow     = token  $(switch [| case _ of "->" -> pure (); "→" -> pure () |])
arrow'    = token' $(switch [| case _ of "->" -> pure (); "→" -> pure () |])
prod      = token  $(switch [| case _ of "*"  -> pure (); "×" -> pure () |])
braceR'   = $(sym' "}")
sqL       = $(sym  "[")
sqL'      = $(sym' "[")
sqR'      = $(sym' "]")
bind      = (BName <$> ident) <|> do {p <- getPos; $(sym "_"); pure $ BDontBind p}
bind'     = bind `pcut` Lit "binder"
decimal'  = token' FP.anyAsciiDecimalWord
hash      = $(sym "#")

sepBy :: Parser a -> Parser sep -> Parser [a]
sepBy pa psep = sepBy1 pa psep <|> pure []

sepBy1 :: Parser a -> Parser sep -> Parser [a]
sepBy1 pa psep = (:) <$> pa <*> FP.many (psep *> pa)

skippedToVar :: Pos -> Parser Tm
skippedToVar l = do {manyIdentChars; r <- getPos; ws; pure $ Ident (Span l r)}
{-# noinline skippedToVar #-}

skipToVar :: Pos -> Parser Tm -> Parser Tm
skipToVar l k = FP.branch identChar (skippedToVar l) (do {r <- getPos; ws; k})
{-# inline skipToVar #-}

atom :: Parser Tm
atom = getPos >>= \p -> $(FP.switch [| case _ of
  "("    -> do {ws; t <- tm'; parR'; pure t}
  "U"    -> skipToVar p do {ws; pure $ U p}
  "0"    -> do {ws; pure $ I0 p}
  "1"    -> do {ws; pure $ I1 p}
  "I"    -> do {ws; pure $ I p}
  "refl" -> skipToVar p do {p' <- getPos; ws; pure $ Refl p p'}
  "@@"   -> do {ws;
                n  <- decimal';
                n' <- FP.optional
                        (hash *> (Lvl <$> (FP.anyAsciiDecimalWord `pcut` Lit "a level expression")));
                p' <- getPos;
                ws;
                pure $ TopLvl p (Lvl n) n' p'}
  "@"    -> do {ws;
                n <- FP.anyAsciiDecimalWord `pcut` Lit "level";
                p' <- getPos;
                pure $ LocalLvl p (Lvl n) p'}
  "?"    -> do {ws; Hole p <$> optional bind}
  _      -> do {ws; Ident <$> ident}
  |])

atom' :: Parser Tm
atom' = atom `cut` atomErr

goProj :: Tm -> Parser Tm
goProj t =
  FP.branch dot
    (    do {p <- rightPos <$> $(sym "1"); goProj (Proj1 t p)}
     <|> do {p <- rightPos <$> $(sym "₁"); goProj (Proj1 t p)}
     <|> do {p <- rightPos <$> $(sym "2"); goProj (Proj2 t p)}
     <|> do {p <- rightPos <$> $(sym "₂"); goProj (Proj2 t p)}
     <|> do {x <- ident; goProj (ProjField t x)}
    )
    (do {p <- rightPos <$> $(sym "⁻¹"); goProj (Sym t p)} <|> pure t)

proj' :: Parser Tm
proj' = (goProj =<< atom') `cut` projErr

proj :: Parser Tm
proj = goProj =<< atom

int :: Parser Tm
int = getPos >>= \p -> $(switch [| case _ of
  "0" -> do {ws; pure (I0 p)}
  "1" -> do {ws; pure (I1 p)}
  "@" -> do {n <- FP.anyAsciiDecimalWord; p' <- getPos; ws; pure $ ILvl p (coerce n) p'}
  _   -> do {ws; Ident <$> ident}
  |])

int' :: Parser Tm
int' = int `pcut` Lit "interval expression"

cof' :: Parser Cof
cof' = do
  i <- int'
  $(sym "=") `pcut` Lit ("\"=\"")
  j <- int'
  pure (CEq i j)

cof :: Parser Cof
cof = do
  i <- int
  $(sym "=") `pcut` Lit ("\"=\"")
  j <- int'
  pure (CEq i j)

goSys1 :: Parser Sys
goSys1 =
      (SCons <$> (semi *> cof' <* dot') <*> tm' <*> goSys1)
  <|> pure SEmpty

goSys :: Parser Sys
goSys =
      (SCons <$> (cof <* dot') <*> tm' <*> goSys1)
  <|> pure SEmpty

sysBindMaybe :: Parser BindMaybe
sysBindMaybe = getPos >>= \p ->
  FP.withOption bind
    (\x -> do {t <- dot' *> tm'; pure $ BMBind x t})
    (BMDontBind <$> (dot' *> tm'))

goSysHCom1 :: Parser SysHCom
goSysHCom1 =
      (SHCons <$> getPos <*> (semi *> cof') <*> sysBindMaybe <*> goSysHCom1)
  <|> pure SHEmpty

goSysHCom :: Parser SysHCom
goSysHCom =
      (SHCons <$> getPos <*> cof <*> sysBindMaybe <*> goSysHCom1)
  <|> pure SHEmpty

sys :: Parser (Sys, Pos)
sys = do
  sqL
  s <- goSys
  p <- rightPos <$> sqR'
  pure (s, p)

sys' :: Parser (Sys, Pos)
sys' = do
  sqL'
  s <- goSys
  p <- rightPos <$> sqR'
  pure (s, p)

sysHCom' :: Parser (SysHCom, Pos)
sysHCom' = do
  sqL'
  s <- goSysHCom
  p <- rightPos <$> sqR'
  pure (s, p)

goApp :: Tm -> Parser Tm
goApp t =
      do {p <- getPos; l <- braceL *> tm' <* braceR'; r <- braceL' *> tm' <* braceR'; u <- proj';
          goApp (PApp p l r t u)}
  <|> do {u <- proj; goApp (App t u)}
  <|> pure t

bindMaybe' :: Parser BindMaybe
bindMaybe' =
  FP.withOption (parL *> bind <* dot)
    (\x -> BMBind x <$> (tm' <* parR'))
    (BMDontBind <$> proj')

goCoe :: Pos -> Parser Tm
goCoe p = do
  r  <- int'
  r' <- int'
  a  <- bindMaybe'
  t  <- proj'
  goApp $ Coe p r r' a t

goCom :: Pos -> Parser Tm
goCom p = do
  r   <- int'
  r'  <- int'
  a   <- bindMaybe'
  sys <- fst <$> sysHCom'
  t   <- proj'
  goApp $ Com p r r' a sys t

goGlue :: Pos -> Parser Tm
goGlue p = do
  base         <- proj'
  (!sys1, !p') <- sys'
  sys2         <- optional sys
  case sys2 of
    Nothing         -> pure $ GlueTm p base Nothing sys1 p'
    Just (sys2, p') -> pure $ GlueTm p base (Just sys1) sys2 p'

goCase :: Pos -> Parser Tm
goCase p = do
  t <- proj'
  b <- optional ((//) <$!> (parL *> bind) <*!> (dot' *> tm' <* parR'))
  sqL'
  let case_ = do
        some bind >>= \case
          [] -> impossible
          x:xs -> do
            dot'
            body <- tm'
            pure (x, xs, body)
  cases <- sepBy case_ semi
  p' <- rightPos <$> sqR'
  goApp $ Case p t b cases p'

goSplit :: Pos -> Parser Tm
goSplit p = do
  let case_ = do
        some bind >>= \case
          [] ->
            impossible
          x:xs -> do
            dot'
            body <- tm'
            pure (x, xs, body)
  cases <- sepBy case_ semi
  p' <- rightPos <$> sqR'
  goApp $ Split p cases p'

goHCom :: Pos -> Parser Tm
goHCom p = do
  t <- HCom p <$> int' <*> int' <*> optional proj <*> (fst <$> sysHCom') <*> proj'
  goApp t

goGlueTy :: Pos -> Parser Tm
goGlueTy p = do
  a <- proj'
  (s, p') <- sys'
  goApp (GlueTy p a s p')

skippedToApp :: Pos -> Parser Tm
skippedToApp l = do
  manyIdentChars
  r <- getPos
  ws
  goApp =<< goProj (Ident (Span l r))
{-# noinline skippedToApp #-}

skipToApp :: Pos -> Parser Tm -> Parser Tm
skipToApp l k = FP.branch identChar (skippedToApp l) (do {r <- getPos; ws; k})
{-# inline skipToApp #-}

appBase :: Parser Tm
appBase = getPos >>= \p -> $(switch [| case _ of
  "λ"      -> skipToApp p do {ws; sqL'; goSplit p}
  "coe"    -> skipToApp p do {ws; goCoe p}
  "case"   -> skipToApp p do {ws; goCase p}
  "hcom"   -> skipToApp p do {ws; goHCom p}
  "com"    -> skipToApp p do {ws; goCom p}
  "unglue" -> skipToApp p do {ws; goApp =<< (Unglue p <$> proj')}
  "ap"     -> skipToApp p do {ws; goApp =<< (Ap p <$> proj' <*> proj')}
  "Glue"   -> skipToApp p do {ws; goGlueTy p}
  "glue"   -> skipToApp p do {ws; goGlue p} |])

-- app :: Parser Tm
-- app = appBase <|> (goApp =<< proj)

app' :: Parser Tm
app' = (appBase <|> (goApp =<< proj')) `cut` appErr

trans' :: Parser Tm
trans' = FP.chainl Trans app' ($(sym "∙") *> app')

eq' :: Parser Tm
eq' = do
  t <- trans'
  FP.branch $(sym "=")
    (do FP.branch braceL
          (do a <- FP.withOption (bind <* dot)
                      (\x -> BMBind x <$> tm')
                      (BMDontBind <$> tm')
              braceR'
              DepPath a t <$> trans')
          (Path t <$> trans'))
    (pure t)

sigma' :: Parser Tm
sigma' = getPos >>= \p ->
  FP.withOption (parL *> bind <* colon)
    (\x -> do a <- tm'
              p' <- rightPos <$> parR'
              FP.branch prod
                (Sg p x a <$> sigma')
                (pure $ Wrap p x a p'))
    (do p' <- getPos
        t <- eq'
        FP.branch prod
          (Sg p (BDontBind p') t <$> sigma')
          (pure t))

piBinder :: Parser ([Bind], Ty, Pos)
piBinder = do
  parL
  bs <- some bind
  colon'
  a <- tm'
  p <- rightPos <$> parR'
  pure (bs, a, p)

pi' :: Parser Tm
pi' = do
  p <- getPos
  FP.withOption (some piBinder)

    (\case
        [([x], a, p')] ->
          FP.branch arrow
            (Pi p x a <$> pi') $
            FP.branch prod
              (do p' <- getPos
                  dom <- Sg p x a <$> sigma'
                  FP.branch arrow
                    (Pi p (BDontBind p') a <$> pi')
                    (pure dom)
              )
              (pure (Wrap p x a p'))

        bs -> do
          arrow'
          b <- pi'
          pure $! foldr'
            (\(!xs, !a, !p') t -> foldr' (\x b -> Pi p' x a b) t xs)
            b bs
    )

    (do p' <- getPos
        t <- sigma'
        FP.branch arrow
          (Pi p (BDontBind p') t <$> pi')
          (pure t))

data LamBind = LBind Bind LamAnnot | LPLam Tm Tm Bind

lamBind :: Parser LamBind
lamBind =
      do {l <- braceL *> tm' <* braceR'; r <- braceL' *> tm' <* braceR';
          x <- bind'; pure $ LPLam l r x}
  <|> do {parL; x <- bind'; colon'; a <- tm'; parR'; pure (LBind x (LAAnn a))}
  <|> (LBind <$> bind <*> pure LANone)

goLam :: Pos -> Parser Tm
goLam p = do
  bs <- some lamBind
  dot'
  t <- lamlet'
  pure $! foldr'
    (\b t -> case b of
        LBind x ma  -> Lam p x ma t
        LPLam l r x -> PLam p l r x t)
    t bs

-- | Desugar Coq-style definition args.
desugarIdentArgs :: [([Bind], Ty, Pos)] -> Maybe Ty -> Tm -> (Tm, Maybe Ty)
desugarIdentArgs args mty rhs = case mty of

  -- if there's no return type annotation, we desugar to annotated lambdas
  Nothing -> let
    tm = foldr' (\(xs, a, p) t -> foldr' (\x t -> Lam p x (LAAnn a) t) t xs) rhs args
    in tm // Nothing

  -- if there's a return type, we annotate the let with a Pi *and* annotate the
  -- lambdas. This is a simple way to get a term representation of the binder
  -- type. However, since we do this pre-elaboration, the annotation has to be
  -- elaborated twice.
  -- TODO: avoid the extra cost.
  Just a  -> let
    tm = foldr' (\(xs, a, p) t -> foldr' (\x t -> Lam p x (LADesugared a) t) t xs) rhs args
    ty = foldr' (\(xs, a, p) b -> foldr' (\x -> Pi p x a) b xs) a args
    in tm // Just ty

goLet :: Pos -> Parser Tm
goLet p = do
  x <- ident'
  args <- many piBinder
  ma   <- optional (colon *> tm')
  assign'
  t <- tm'
  (t, ma) <- pure $! desugarIdentArgs args ma t
  semi'
  u <- lamlet'
  pure $ Let p x ma t u

lamlet' :: Parser Tm
lamlet' = getPos >>= \p -> $(switch [| case _ of
  "λ"   -> skipToApp p do {ws; FP.branch sqL (goSplit p) (goLam p)}
  "\\"  -> ws >> FP.branch sqL (goSplit p) (goLam p)
  "let" -> skipToApp p do {ws; goLet p}
  _     -> pi' |])

tm' :: Parser Tm
tm' = do
  t <- lamlet'
  FP.branch comma (Pair t <$> tm') (pure t)

telBinder :: Parser ([Bind], Ty)
telBinder =
      do {parL; bs <- some bind; colon; t <- tm'; parR'; pure (bs, t)}
  <|> do {p <- getPos; t <- proj; pure ([BDontBind p], t)}

telescope :: Parser [(Bind, Ty)]
telescope = do
  bs <- many telBinder
  pure $! foldr' (\(!xs, !a) acc -> foldr' (\x acc -> (x, a):acc) acc xs) [] bs

modulePath :: Parser String
modulePath =
  FP.withByteString (FP.skipSome (FP.satisfy \c -> isAlphaNum c || c == '.') <* ws) \_ bstr ->
  pure $! FP.utf8ToStr bstr

modulePath' :: Parser String
modulePath' = modulePath `pcut` Lit "a module path"

top' :: Parser Top
top' =
  FP.withOption ((//) <$!> getPos <*> ($(kw "higher") *> $(kw' "inductive") *> ident'))
    (\(pos, x) -> do
        params <- telescope
        assign'
        constructors <-
          sepBy ((,,) <$!> ident <*!> telescope <*!> optional (fst <$> sys))
                ($(sym "|"))
        semi'
        u <- top'
        pure $! THData pos x params constructors u
    )

    (FP.withOption ((//) <$!> getPos <*> ($(kw "inductive") *> ident'))
      (\(pos, x) -> do
          params <- telescope
          assign'
          constructors <- sepBy ((,) <$!> ident <*!> telescope) $(sym "|")
          semi'
          u <- top'
          pure $! TData pos x params constructors u
      )

      (FP.withOption ((//) <$!> getPos <*!> ident)
        (\(pos, x) -> do
          args <- many piBinder
          ma   <- optional (colon *> tm')
          assign'
          t <- tm'
          (t, ma) <- pure $! desugarIdentArgs args ma t
          semi'
          u <- top'
          pure $! TDef pos x ma t u)

        (FP.withOption ((//) <$!> getPos <*!> ( $(kw "import") *> modulePath'))
          (\(pos, file) -> do
              semi'
              u <- top'
              pure $ TImport pos file u)
          (pure TEmpty))))

src :: Parser (Maybe String, Top)
src = do
  ws
  mod <- optional ($(kw "module") *> modulePath' <* semi')
  t   <- top'
  eof `pcut` Lit "end of file"
  pure (mod, t)

parseByteString :: FilePath -> B.ByteString -> IO (Maybe String, Top)
parseByteString path s = do
  let env = SrcFile path s
  case FP.runParser src env 0 s of
    OK t _ _ -> pure t
    Fail     -> impossible
    Err e    -> do putStrLn $ prettyError env e
                   exitFailure

parseString :: FilePath -> String -> IO (Maybe String, Top)
parseString path s = parseByteString path (FP.strToUtf8 s)

parseStdin :: IO (Maybe String, Top, B.ByteString)
parseStdin = do
  s        <- B.getContents
  (!m, !t) <- parseByteString "(stdin)" s
  pure (m, t, s)
