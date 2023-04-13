
module Pretty (
    type Names
  , type Shadow
  , type PrettyArgs
  , type NameKey(..)
  , Pretty(..)) where

import Prelude hiding (pi)
import Data.String
import qualified Data.Map.Strict as M

import Common
import CoreTypes
import Interval
import ElabState
import Data.Foldable

--------------------------------------------------------------------------------

ifVerbose :: a -> a -> a
ifVerbose t f = runIO $ getTop <&> (^.printingOpts.verbose) >>= \case
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

data NameKey = NKLocal Lvl | NKTop Lvl | NKLocalI IVar | NKDCon Lvl Lvl deriving (Eq, Ord, Show)

type Prec     = (?prec   :: Int)
type Names    = (?names  :: M.Map NameKey Name)
type Shadow   = (?shadow :: M.Map Name Int)

showVar :: M.Map NameKey Name -> NameKey -> String
showVar m k =
  let gokey = case k of
        NKLocal x  -> '@':show x
        NKTop x    -> "@@"++show x
        NKLocalI x -> "@"++show x
        NKDCon i j -> "@@"++show i++"#"++show j
  in case M.lookup k m of
    Nothing      -> "(ERR " ++ show k ++ ")"
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

dataCon :: PrettyArgs (Lvl -> Lvl -> Txt)
dataCon i j = str (?names `showVar` NKDCon i j)

spine :: PrettyArgs (Spine -> Txt)
spine = \case
  SPNil         -> mempty
  SPCons t sp   -> " " <> proj t <> spine sp

caseBody :: PrettyArgs ([Name] -> Tm -> Txt)
caseBody xs t = case xs of
  []   -> ". " <> proj t
  [x]  -> fresh x \x -> " " <> x <> ". " <> proj t
  x:xs -> fresh x \x -> " " <> x <> caseBody xs t

cases :: PrettyArgs (Cases -> Txt)
cases = \case
  CSNil               -> mempty
  CSCons x xs t CSNil -> str x <> caseBody xs t
  CSCons x xs t cs    -> str x <> caseBody xs t <> "; " <> cases cs

coeTy :: PrettyArgs (Txt -> Tm -> Txt)
coeTy i (PApp _ _ t@LocalVar{} (IVar x)) | x == ?idom - 1 = " " <> proj t <> " "
coeTy i (LApp t@LocalVar{} (IVar x)) | x == ?idom - 1 = " " <> proj t <> " "
coeTy i t = " (" <> i <> ". " <> pair t <> ") "

unProject :: Tm -> Name -> Maybe Tm
unProject t x = case t of
  Proj2 t x' | x == x' -> Nothing
             | True    -> unProject t x
  t                    -> Just t

tm :: Prec => PrettyArgs (Tm -> Txt)
tm = \case
  TopVar x _            -> topVar x
  RecursiveCall x       -> topVar x
  LocalVar x            -> str (?names `showVar` NKLocal (?dom - coerce x - 1))
  Let x a t u           -> let pa = let_ a; pt = let_ t in fresh x \x ->
                           letp ("let " <> x <> " : " <> pa <> " := " <> pt <> "; " <> tm u)
  Pi "_" a b            -> let pa = sigma a in fresh "_" \_ ->
                           pip (pa <> " → " <> pi b)
  Pi n a b              -> let pa = pair a in fresh n \n ->
                           pip (piBind n pa  <> goLinesPis b)
  App t u               -> appp (app t <> " " <> proj u)
  Lam x t               -> letp (fresh x \x -> "λ " <> x <> goLams t)
  Line "_" a            -> freshI "_" \_ -> pip ("I → " <> pi a)
  Line x a              -> freshI x   \x -> pip (lineBind x <> goLinesPis a)
  LApp t u              -> appp (app t <> " " <> int u)
  LLam x t              -> letp (freshI x \x -> "λ " <> x <> goLams t)
  Sg "_" a b            -> let pa = eq a in fresh "_" \_ ->
                           sigmap (pa <> " × " <> sigma b)
  Sg x a b              -> let pa = pair a in fresh x \x ->
                           sigmap ("(" <> x <> " : " <> pa <> ") × " <> sigma b)
  Pair x t u            -> pairp (let_ t <> ", " <> pair u)
  Proj1 t x             -> case unProject t x of
                             Nothing -> projp (proj t <> ".1")
                             Just t  -> projp (proj t <> "." <> str x)
  Proj2 t x             -> projp (proj t <> ".2")
  U                     -> "U"
  Path "_" a t u        -> ifVerbose
                            (let pt = trans t; pu = trans u in freshI "_" \_ ->
                             eqp (pt <> " ={" <> "_" <> ". " <> pair a <> "} " <> pu))
                            (eqp (trans t <> " = " <> trans u))
  Path x a t u          -> let pt = trans t; pu = trans u in freshI x \x ->
                           eqp (pt <> " ={" <> x <> ". " <> pair a <> "} " <> pu)
  PApp l r t u          -> ifVerbose
                             (appp (app t <> " {" <> pair l <> "} {" <> pair r <> "} " <> int u))
                             (appp (app t <> " " <> int u))
  PLam l r x t          -> ifVerbose
                             (let pl = pair l; pr = pair r in
                              letp (freshI x \x -> "λ {" <> pl <> "} {" <> pr <> "} " <> x <> goLams t))
                             (letp (freshI x \x -> "λ " <> x <> goLams t))
  Coe r r' i a t        -> let pt = proj t; pr = int r; pr' = int r' in freshI i \i ->
                           appp ("coe " <> pr <> " " <> pr' <> coeTy i a <> pt)
  HCom r r' a t u       -> appp ("hcom " <> int r <> " " <> int r'
                                 <> ifVerbose (" " <> proj a) ""
                                 <> " " <> sysH t <> " " <> proj u)
  GlueTy a s            -> appp ("Glue " <> proj a <> " " <> sys s)
  Unglue t _            -> appp ("unglue " <> proj t)
  Glue a s1 s2          -> ifVerbose
                             (appp ("glue " <> proj a <> " " <> sys s1 <> " " <> sys s2))
                             (appp ("glue " <> proj a <> " " <> sys s2))
  Hole i p              -> case i of
                             Just x -> "?" <> str x
                             _      -> runIO $ (getTop <&> (^.printingOpts.errPrinting)) >>= \case
                               True -> pure ("?" <> str (sourcePosPretty (coerce p :: SourcePos)))
                               _    -> pure "?"
  Com r r' i a t u      -> appp (let pr = int r; pr' = int r'; pt = sysH t; pu = proj u in freshI i \i ->
                           "com " <> pr <> " " <> pr' <> " (" <> i <> ". " <> pair a <> ") "
                                  <> pt <> " " <> pu)
  WkI x t               -> wkI x (tm t)
  Refl _                -> "refl"
  Sym _ _ _ p           -> projp (proj p <> "⁻¹")
  Trans _ _ _ _ p q     -> transp (app p <> " ∙ " <> trans q)
  Ap f _ _ p            -> appp ("ap " <> proj f <> " " <> proj p)
  TyCon x SPNil         -> topVar x
  TyCon x ts            -> appp (topVar x <> spine ts)
  DCon (CI i j _) SPNil -> dataCon i j
  DCon (CI i j _) sp    -> appp (dataCon i j <> spine sp)
  Case t x b cs         -> ifVerbose
                            (let pt = proj t; pcs = cases cs in fresh x \x ->
                             appp ("case " <> pt <> " (" <> x <> ". " <> tm b <> ") [" <> pcs <> "]"))
                            (appp ("case " <> proj t <> " [" <> cases cs <> "]"))
  Wrap x a              -> "(" <> str x <> " : " <> pair a <> ")"
  Pack x t              -> tm t
  Unpack t x            -> case unProject t x of
                             Nothing -> projp (proj t <> ".1")
                             Just t  -> projp (proj t <> "." <> str x)
  Split x b cs          -> appp ("λ[" <> cases cs <> "]")

----------------------------------------------------------------------------------------------------

dataFields :: PrettyArgs (Tel -> Txt)
dataFields = \case
  TNil         -> mempty
  TCons x a fs -> let pa = pair a in fresh x \x ->
                  "(" <> x <> " : " <> pa <> ")" <> dataFields fs

dataCons :: PrettyArgs ([(Name, Tel)] -> Txt)
dataCons = \case
  []         -> mempty
  [(x, fs)]  -> str x <> dataFields fs
  (x, fs):cs -> str x <> dataFields fs <> "\n  | " <> dataCons cs

inductive :: PrettyArgs (Tel -> [(Name, Tel)] -> Txt)
inductive ps cs = case ps of
  TNil         -> " :=\n    " <> dataCons cs
  TCons x a ps -> let pa = pair a in fresh x \x ->
                  " (" <> x <> " : " <> pa <> ")" <> inductive ps cs

top_ :: Names => LvlArg => Top -> Txt
top_ = \case
  TEmpty       -> mempty
  TDef x a t u ->
    let ?dom    = 0
        ?idom   = 0
        ?names  = M.insert (NKTop ?lvl) x ?names
        ?lvl    = ?lvl + 1
        ?shadow = mempty in
    "\n" <> str x <> " : " <> pair a <> " :=\n  " <> pair t <> ";\n" <> top_ u
  TData x ps cons top ->
    let ?dom    = 0
        ?idom   = 0
        ?shadow = mempty
        ?lvl    = ?lvl + 1
        ?names  = foldl'
           (\ns (!conid, !x) -> M.insert (NKDCon ?lvl conid) x ns)
           (M.insert (NKTop ?lvl) x ?names)
           (zipWith (\conid (x, _) -> (conid, x)) [0..] cons) in
    "\ndata " <> str x <> inductive ps cons <> ";\n" <> top_ top

----------------------------------------------------------------------------------------------------

class Pretty c c0 a | a -> c c0 where
  pretty    :: c => a -> String
  pretty0   :: c0 => a -> String
  prettydbg :: a -> String -- ^ Print all vars as indices.

instance Pretty () () Top where
  pretty  t   = let ?names = mempty; ?lvl = 0 in runTxt (top_ t)
  pretty0 t   = let ?names = mempty; ?lvl = 0 in runTxt (top_ t)
  prettydbg t = let ?names = mempty; ?lvl = 0 in runTxt (top_ t)

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
