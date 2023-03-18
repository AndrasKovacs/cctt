
module Pretty (
    type Names
  , type Shadow
  , type PrettyArgs
  , type NameKey(..)
  , setVerbosity
  , getVerbosity
  , Pretty(..)) where

import Prelude hiding (pi)
import Data.String
import qualified Data.Map.Strict as M
import Data.IORef

import Common
import CoreTypes
import Interval

-- import Debug.Trace

--------------------------------------------------------------------------------

-- | When verbosity is true, we print all hcom base types and all path abstraction/application
--   endpoints.
verbosity :: IORef Bool
verbosity = runIO $ newIORef False
{-# noinline verbosity #-}

getVerbosity :: IO Bool
getVerbosity = readIORef verbosity

setVerbosity :: Bool -> IO ()
setVerbosity = writeIORef verbosity

ifVerbose :: a -> a -> a
ifVerbose t f = runIO $ getVerbosity >>= \case
  True  -> pure t
  False -> pure f
{-# inline ifVerbose #-}

--------------------------------------------------------------------------------

newtype Txt = Txt (String -> String)

runTxt :: Txt -> String
runTxt (Txt f) = f ""

instance Semigroup Txt where
  Txt x <> Txt y = Txt (x . y); {-# inline (<>) #-}

instance Monoid Txt where
  mempty = Txt id; {-# inline mempty #-}

instance IsString Txt where
  fromString s = Txt (s++); {-# inline fromString #-}

instance Show Txt where
  show (Txt s) = s ""

str    = fromString; {-# inline str #-}
char c = Txt (c:); {-# inline char #-}

data NameKey = NKLocal Lvl | NKTop Lvl | NKLocalI IVar deriving (Eq, Ord)

type Prec     = (?prec   :: Int)
type Names    = (?names  :: M.Map NameKey Name)
type Shadow   = (?shadow :: M.Map Name Int)

showVar :: M.Map NameKey Name -> NameKey -> String
showVar m k =
  let gokey = case k of
        NKLocal x  -> '@':show x
        NKTop x    -> "@@"++show x
        NKLocalI x -> "@"++show x
  in case M.lookup k m of
    Nothing      -> gokey
    Just ('_':_) -> gokey
    Just n       -> n

type PrettyArgs a = Names => Shadow => DomArg => IDomArg => a

par :: Prec => Int -> Txt -> Txt
par p s | p < ?prec = char '(' <> s <> char ')'
        | True      = s
{-# inline par #-}

projp  s = par 7 s; {-# inline projp #-}
appp   s = par 6 s; {-# inline appp #-}
transp s = par 5 s; {-# inline transp #-}
eqp    s = par 4 s; {-# inline eqp #-}
sigmap s = par 3 s; {-# inline sigmap #-}
pip    s = par 2 s; {-# inline pip #-}
letp   s = par 1 s; {-# inline letp #-}
pairp  s = par 0 s; {-# inline pairp #-}

--------------------------------------------------------------------------------

freshen :: Name -> Int -> Name
freshen "_" n = "_"
freshen x   n = case n of 0 -> x; n -> x ++ show n

fresh :: Name -> PrettyArgs (Txt -> a) -> PrettyArgs a
fresh x act   =
  let fresh   = ?dom
      sh      = maybe 0 id (M.lookup x ?shadow)
      newname = freshen x sh in
  let ?dom    = fresh + 1
      ?shadow = M.insert x (sh + 1) ?shadow
      ?names  = M.insert (NKLocal fresh) newname ?names in
  act (str (newname))
{-# inline fresh #-}

freshI :: Name -> PrettyArgs (Txt -> a) -> PrettyArgs a
freshI x act =
  let fresh   = ?idom
      sh      = maybe 0 id (M.lookup x ?shadow)
      newname = freshen x sh in
  let ?idom   = fresh + 1
      ?shadow = M.insert x (sh + 1) ?shadow
      ?names  = M.insert (NKLocalI fresh) newname ?names in
  act (str (newname))
{-# inline freshI #-}

wkI :: Name -> PrettyArgs a -> PrettyArgs a
wkI x act =
  let lastI   = ?idom - 1 in
  let ?idom   = lastI
      ?names  = M.delete (NKLocalI lastI) ?names
      ?shadow = M.update (\case 1 -> Nothing; n -> Just (n - 1)) x ?shadow in
  act
{-# inline wkI #-}

proj  x = doTm 7 x; {-# inline proj #-}
app   x = doTm 6 x; {-# inline app #-}
trans x = doTm 5 x; {-# inline trans #-}
eq    x = doTm 4 x; {-# inline eq #-}
sigma x = doTm 3 x; {-# inline sigma #-}
pi    x = doTm 2 x; {-# inline pi #-}
let_  x = doTm 1 x; {-# inline let_ #-}
pair  x = doTm 0 x; {-# inline pair #-}

doTm :: PrettyArgs (Int -> Tm -> Txt)
doTm p t = let ?prec = p in tm t; {-# inline doTm #-}

piBind :: Txt -> Txt -> Txt
piBind n a = "(" <> n <> " : " <> a <> ")"; {-# inline piBind #-}

lineBind :: Txt -> Txt
lineBind n = "(" <> n <> " : I)"; {-# inline lineBind #-}

goLinesPis :: PrettyArgs (Tm -> Txt)
goLinesPis = \case
  Pi x a b | x /= "_" ->
    let pa = pair a in fresh x \x ->
    piBind x pa <> goLinesPis b
  Line x b | x /= "_" ->
    freshI x \x -> lineBind x <> goLinesPis b
  t ->
    " → " <> pi t

goLams :: PrettyArgs (Tm -> Txt)
goLams = \case
  Lam x t      -> fresh  x \x -> " " <> x <> goLams t
  PLam l r x t -> ifVerbose
                    (let pl = pair l; pr = pair r in
                     freshI x \x -> " {" <> pl <> "} {" <> pr <> "} " <> x <> goLams t)
                    (freshI x \x -> " " <> x <> goLams t)
  LLam x t     -> freshI x \x -> " " <> x <> goLams t
  t            -> ". " <> let_ t

int :: PrettyArgs (I -> Txt)
int = \case
  I0     -> "0"
  I1     -> "1"
  IVar x -> str (showVar ?names (NKLocalI x))

cofEq :: PrettyArgs (CofEq -> Txt)
cofEq (CofEq i j) = int i <> " = " <> int j

cof :: PrettyArgs (Cof -> Txt)
cof = \case
  CTrue         -> "⊤"
  CAnd eq CTrue -> cofEq eq
  CAnd eq c     -> cofEq eq <> " , " <> cof c

goSysH :: PrettyArgs (SysHCom -> Txt)
goSysH = \case
  SHEmpty              -> mempty
  SHCons c x t SHEmpty -> let pc = cof c in freshI x \x ->
                          pc <> " " <> x <> ". " <> pair t
  SHCons c x t sys     -> let pc = cof c; psys = goSysH sys in freshI x \x ->
                          pc <> " " <> x <> ". " <> pair t <> "; " <> psys

sysH :: PrettyArgs (SysHCom -> Txt)
sysH s = "[" <> goSysH s <> "]"

goSys :: PrettyArgs (Sys -> Txt)
goSys = \case
  SEmpty           -> mempty
  SCons c t SEmpty -> cof c <> ". " <> pair t
  SCons c t sys    -> cof c <> ". " <> pair t <> "; " <> goSys sys

sys :: PrettyArgs (Sys -> Txt)
sys s = "[" <> goSys s <> "]"

topVar :: PrettyArgs (Lvl -> Txt)
topVar x = str (?names `showVar` NKTop x)

dSpine :: PrettyArgs (DSpine -> Txt)
dSpine = \case
  DNil         -> mempty
  DInd t sp    -> " " <> proj t <> dSpine sp
  DHInd t _ sp -> " " <> proj t <> dSpine sp
  DExt t _ sp  -> " " <> proj t <> dSpine sp

sepby :: (a -> Txt) -> [a] -> Txt -> Txt
sepby f []     sep = mempty
sepby f [a]    sep = f a
sepby f (a:as) sep = f a <> sep <> sepby f as sep
{-# inline sepby #-}

methods :: PrettyArgs (Methods -> Txt)
methods = \case
  MNil            -> mempty
  MCons xs t MNil -> sepby str xs " " <> ". " <> proj t
  MCons xs t ms   -> sepby str xs " " <> ". " <> proj t <> "; " <> methods ms

tyParams :: PrettyArgs (TyParams -> Txt)
tyParams = \case
  TPNil          -> mempty
  TPSnoc TPNil t -> proj t
  TPSnoc ts t    -> tyParams ts <> " " <> proj t

coeTy :: PrettyArgs (Txt -> Tm -> Txt)
coeTy i (PApp _ _ t@LocalVar{} (IVar x)) | x == ?idom - 1 = " " <> proj t <> " "
coeTy i (LApp t@LocalVar{} (IVar x)) | x == ?idom - 1 = " " <> proj t <> " "
coeTy i t = " (" <> i <> ". " <> pair t <> ") "

tm :: Prec => PrettyArgs (Tm -> Txt)
tm = \case
  TopVar x _        -> topVar x
  LocalVar x        -> str (?names `showVar` NKLocal (?dom - coerce x - 1))
  Let x a t u       -> let pa = let_ a; pt = let_ t in fresh x \x ->
                       letp ("let " <> x <> " : " <> pa <> " := " <> pt <> "; " <> tm u)
  Pi "_" a b        -> let pa = sigma a in fresh "_" \_ ->
                       pip (pa <> " → " <> pi b)
  Pi n a b          -> let pa = pair a in fresh n \n ->
                       pip (piBind n pa  <> goLinesPis b)
  App t u           -> appp (app t <> " " <> proj u)
  Lam x t           -> letp (fresh x \x -> "λ " <> x <> goLams t)
  Line "_" a        -> freshI "_" \_ -> pip ("I → " <> pi a)
  Line x a          -> freshI x   \x -> pip (lineBind x <> goLinesPis a)
  LApp t u          -> appp (app t <> " " <> int u)
  LLam x t          -> letp (freshI x \x -> "λ " <> x <> goLams t)
  Sg "_" a b        -> let pa = eq a in fresh "_" \_ ->
                       sigmap (pa <> " × " <> sigma b)
  Sg x a b          -> let pa = pair a in fresh x \x ->
                       sigmap ("(" <> x <> " : " <> pa <> ") × " <> sigma b)
  Pair t u          -> pairp (let_ t <> ", " <> pair u)
  Proj1 t           -> projp (proj t <> ".1")
  Proj2 t           -> projp (proj t <> ".2")
  U                 -> "U"
  Path "_" _ t u    -> eqp (trans t <> " = " <> trans u)
  Path x a t u      -> let pt = trans t; pu = trans u in freshI x \x ->
                       eqp (pt <> " ={" <> x <> ". " <> pair a <> "} " <> pu)
  PApp l r t u      -> ifVerbose
                         (appp (app t <> " {" <> pair l <> "} {" <> pair r <> "} " <> int u))
                         (appp (app t <> " " <> int u))
  PLam l r x t      -> ifVerbose
                         (let pl = pair l; pr = pair r in
                          letp (freshI x \x -> "λ {" <> pl <> "} {" <> pr <> "} " <> x <> goLams t))
                         (letp (freshI x \x -> "λ " <> x <> goLams t))
  Coe r r' i a t    -> let pt = proj t; pr = int r; pr' = int r' in freshI i \i ->
                       appp ("coe " <> pr <> " " <> pr' <> coeTy i a <> pt)
  HCom r r' a t u   -> appp ("hcom " <> int r <> " " <> int r'
                             <> ifVerbose (" " <> proj a) ""
                             <> " " <> sysH t <> " " <> proj u)
  GlueTy a s        -> appp ("Glue " <> proj a <> " " <> sys s)
  Unglue t _        -> appp ("unglue " <> proj t)
  Glue a s1 s2      -> ifVerbose
                         (appp ("glue " <> proj a <> " " <> sys s1 <> " " <> sys s2))
                         (appp ("glue " <> proj a <> " " <> sys s2))
  TODO              -> "TODO"
  Com r r' i a t u  -> appp (let pr = int r; pr' = int r'; pt = sysH t; pu = proj u in freshI i \i ->
                       "com " <> pr <> " " <> pr' <> " (" <> i <> ". " <> pair a <> ") "
                              <> pt <> " " <> pu)
  WkI x t           -> wkI x (tm t)
  Refl _            -> "refl"
  Sym _ _ _ p       -> projp (proj p <> "⁻¹")
  Trans _ _ _ _ p q -> transp (app p <> " ∙ " <> trans q)
  Ap f _ _ p        -> appp ("ap " <> proj f <> " " <> proj p)
  TyCon x TPNil     -> topVar x
  TyCon x ts        -> appp (topVar x <> tyParams ts)
  DCon x _ DNil     -> topVar x
  DCon x _ sp       -> appp (topVar x <> dSpine sp)
  Elim mot met t    -> appp ("elim " <> proj mot <> " [" <> methods met <> "] " <> proj t)


top :: Names => LvlArg => Top -> Txt
top = \case
  TEmpty       -> mempty
  TDef x a t u ->
    let ?dom = 0; ?idom = 0; ?shadow = mempty in
    "\n" <> str x <> " : " <> pair a <> "\n  := " <> pair t <> ";\n" <>
    (let ?names = M.insert (NKTop ?lvl) x ?names; ?lvl = ?lvl + 1 in top u)

----------------------------------------------------------------------------------------------------

class Pretty c c0 a | a -> c c0 where
  pretty    :: c => a -> String
  pretty0   :: c0 => a -> String
  prettydbg :: a -> String -- ^ Print all vars as indices.

instance Pretty () () Top where
  pretty  t   = let ?names = mempty; ?lvl = 0 in runTxt (top t)
  pretty0 t   = let ?names = mempty; ?lvl = 0 in runTxt (top t)
  prettydbg t = let ?names = mempty; ?lvl = 0 in runTxt (top t)

instance Pretty (Names, DomArg, IDomArg) Names Tm where
  pretty    t = let ?shadow = mempty in runTxt (pair t)
  pretty0   t = let ?dom = 0; ?idom = 0; ?shadow = mempty in runTxt (pair t)
  prettydbg t = let ?dom = 0; ?idom = 0; ?shadow = mempty; ?names = mempty in runTxt (pair t)

instance Pretty (Names, DomArg, IDomArg) Names Cof where
  pretty  t = let ?shadow = mempty in runTxt (cof t)
  pretty0 t = let ?dom = 0; ?idom = 0; ?shadow = mempty in runTxt (cof t)
  prettydbg t = let ?dom = 0; ?idom = 0; ?shadow = mempty; ?names = mempty in runTxt (cof t)

instance Pretty (Names, DomArg, IDomArg) Names Sys where
  pretty  t = let ?shadow = mempty in runTxt (sys t)
  pretty0 t = let ?dom = 0; ?idom = 0; ?shadow = mempty in runTxt (sys t)
  prettydbg t = let ?dom = 0; ?idom = 0; ?shadow = mempty; ?names = mempty in runTxt (sys t)
