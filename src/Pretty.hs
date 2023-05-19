
module Pretty (
    type Names(..)
  , type PrettyArgs
  , localsToNames
  , withPrettyArgs
  , withPrettyArgs0
  , bind
  , bindI
  , Pretty(..)) where

import Prelude hiding (pi)
import Data.String

import Common
import CoreTypes
import Cubical hiding (eq)
import ElabState hiding (bind, bindI, isNameUsed)
import qualified Data.LvlMap as LM

--------------------------------------------------------------------------------

localsToNames :: Locals -> Names
localsToNames = \case
  LNil           -> NNil
  LBind ls x _ _ -> NBind (localsToNames ls) x
  LBindI ls x    -> NBindI (localsToNames ls) x
  LCof ls _      -> localsToNames ls

withPrettyArgs :: Elab (PrettyArgs a -> a)
withPrettyArgs act =
  let ?idom  = dom ?cof
      ?names = localsToNames ?locals in
  act
{-# inline withPrettyArgs #-}

ifVerbose :: a -> a -> a
ifVerbose t f = runIO $ getState <&> (^.printingOpts.verbose) >>= \case
  True  -> pure t
  False -> pure f
{-# inline ifVerbose #-}

newtype Txt = Txt (String -> String)

runTxt :: Txt -> String
runTxt (Txt f) = f mempty

instance Semigroup Txt where
  Txt x <> Txt y = Txt (x . y); {-# inline (<>) #-}

instance Monoid Txt where
  mempty = Txt id; {-# inline mempty #-}

instance IsString Txt where
  fromString s = Txt (s++); {-# inline fromString #-}

instance Show Txt where
  show (Txt s) = s mempty

str    = fromString; {-# inline str #-}
char c = Txt (c:); {-# inline char #-}

data Names = NNil | NBind Names Name | NBindI Names Name deriving Show

isNameUsed :: Name -> Names -> Bool
isNameUsed x NNil           = False
isNameUsed x (NBind ns x')  = x == x' || isNameUsed x ns
isNameUsed x (NBindI ns x') = x == x' || isNameUsed x ns

type Prec     = (?prec   :: Int)
type NamesArg = (?names :: Names)

type PrettyArgs a = NamesArg => DomArg => IDomArg => a

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

bind :: Name -> PrettyArgs (Txt -> a) -> PrettyArgs a
bind x act = let ?names = NBind ?names x; ?dom = ?dom + 1 in act (str x)
{-# inline bind #-}

bindI :: Name -> PrettyArgs (Txt -> a) -> PrettyArgs a
bindI x act = let ?names = NBindI ?names x; ?idom = ?idom + 1 in act (str x)
{-# inline bindI #-}

wkI :: PrettyArgs a -> PrettyArgs a
wkI act =
  let ?idom = ?idom - 1
      ?names = case ?names of NBindI ns _ -> ns; _ -> impossible in
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
    let pa = pair a in bind x \x ->
    piBind x pa <> goLinesPis b
  Line x b | x /= "_" ->
    bindI x \x -> lineBind x <> goLinesPis b
  t ->
    " → " <> pi t

goLams :: PrettyArgs (Tm -> Txt)
goLams = \case
  Lam x t      -> bind  x \x -> " " <> x <> goLams t
  PLam l r x t -> ifVerbose
                    (let pl = pair l; pr = pair r in
                     bindI x \x -> " {" <> pl <> "} {" <> pr <> "} " <> x <> goLams t)
                    (bindI x \x -> " " <> x <> goLams t)
  LLam x t     -> bindI x \x -> " " <> x <> goLams t
  t            -> ". " <> let_ t

int :: PrettyArgs (I -> Txt)
int = \case
  I0     -> "0"
  I1     -> "1"
  IVar x -> ivar x

cofEq :: PrettyArgs (I -> I -> Txt)
cofEq i j = int i <> " = " <> int j

necof :: PrettyArgs (NeCof -> Txt)
necof = \case
  NCEq i j -> cofEq i j

cof :: PrettyArgs (Cof -> Txt)
cof = \case
  CEq i j -> cofEq i j

goSysH :: PrettyArgs (SysHCom -> Txt)
goSysH = \case
  SHEmpty              -> mempty
  SHCons c x t SHEmpty -> let pc = cof c in bindI x \x ->
                          pc <> " " <> x <> ". " <> pair t
  SHCons c x t sys     -> let pc = cof c; psys = goSysH sys in bindI x \x ->
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

spine :: PrettyArgs (Spine -> Txt)
spine = \case
  SPNil         -> mempty
  SPCons t sp   -> " " <> proj t <> spine sp

caseBody :: PrettyArgs ([Name] -> Tm -> Txt)
caseBody xs t = case xs of
  []   -> ". " <> pair t
  [x]  -> bind x \x -> " " <> x <> ". " <> pair t
  x:xs -> bind x \x -> " " <> x <> caseBody xs t

hcaseBody' :: PrettyArgs ([Name] -> Tm -> Txt)
hcaseBody' xs t = case xs of
  []   -> ". " <> pair t
  [x]  -> bindI x \x -> " " <> x <> ". " <> pair t
  x:xs -> bindI x \x -> " " <> x <> hcaseBody' xs t

hcaseBody :: PrettyArgs ([Name] -> [Name] -> Tm -> Txt)
hcaseBody xs is t = case xs of
  []   -> hcaseBody' is t
  [x]  -> bind x \x -> " " <> x <> hcaseBody' is t
  x:xs -> bind x \x -> " " <> x <> hcaseBody xs is t

cases :: PrettyArgs (Cases -> Txt)
cases = \case
  CSNil               -> mempty
  CSCons x xs t CSNil -> str x <> caseBody xs t
  CSCons x xs t cs    -> str x <> caseBody xs t <> "; " <> cases cs

hcases :: PrettyArgs (HCases -> Txt)
hcases = \case
  HCSNil                   -> mempty
  HCSCons x xs is t HCSNil -> str x <> hcaseBody xs is t
  HCSCons x xs is t cs     -> str x <> hcaseBody xs is t <> "; " <> hcases cs

coeTy :: PrettyArgs (Txt -> Tm -> Txt)
coeTy i (PApp _ _ t@LocalVar{} (IVar x)) | x == ?idom - 1 = " " <> proj t <> " "
coeTy i (LApp t@LocalVar{} (IVar x)) | x == ?idom - 1 = " " <> proj t <> " "
coeTy i t = " (" <> i <> ". " <> pair t <> ") "

unProject :: Tm -> Name -> Maybe Tm
unProject t x = case t of
  Proj2 t x' | x == x' -> Nothing
             | True    -> unProject t x
  t                    -> Just t

ivar :: PrettyArgs (IVar -> Txt)
ivar i = let
  go 0 (NBindI _ x)  = x // (x == "_")
  go l (NBind ls x)  = case go l ls of
                         (x', sh) -> x' // (sh || x == x')
  go l (NBindI ls x) = case go (l - 1) ls of
                         (x', sh) -> x' // (sh || x == x')
  go _ _             = impossible

  in if i < ?idom then
    case go (lvlToIx (coerce ?idom) (coerce i)) ?names of
      (x, True) -> "@" <> str (show i)
      (x, _   ) -> str x
  else
    "(ERR " <> str (show i) <> ")"

  -- in case go (lvlToIx (coerce ?idom) (coerce i)) ?names of
  --   (x, True) -> "@" <> str (show i)
  --   (x, _   ) -> str x

localVar :: NamesArg => DomArg => Ix -> Txt
localVar i = let

  go :: Ix -> Names -> (Name, Bool)
  go 0 (NBind _ x)   = x // (x == "_")
  go i (NBind ls x)  = case go (i - 1) ls of
                         (x', sh) -> x' // (sh || x == x')
  go i (NBindI ls x) = case go i ls of
                         (x', sh) -> x' // (sh || x == x')
  go _ _             = impossible

  in case go i ?names of
    (x, True) -> "@" <> str (show (ixToLvl ?dom i))
    (x, _   ) -> str x

topName :: PrettyArgs ((t -> Name) -> (t -> Lvl) -> t -> Txt)
topName name id t = if isNameUsed (name t) ?names
  then "@@" <> str (show (id t))
  else str (name t)

dcon :: PrettyArgs (DConInfo -> Txt)
dcon inf = if isNameUsed (inf^.name) ?names
  then "@@" <> str (show (inf^.tyConInfo.tyId)) <> "#" <> str (show (inf^.conId))
  else str (inf^.name)

hdcon :: PrettyArgs (HDConInfo -> Txt)
hdcon inf = if isNameUsed (inf^.name) ?names
  then "@@" <> str (show (inf^.tyConInfo.tyId)) <> "#" <> str (show (inf^.conId))
  else str (inf^.name)

goSub :: PrettyArgs (Sub -> Txt)
goSub (Sub _ _ is) = go is where
  go ILNil        = mempty
  go (ILDef is i) = go is <> " " <> int i

tm :: Prec => PrettyArgs (Tm -> Txt)
tm = \case
  TopVar inf         -> topName (^.name) (^.defId) inf
  RecursiveCall inf  -> topName (^.name) (^.recId) inf
  LocalVar x         -> localVar x
  Let x a t u        -> let pa = let_ a; pt = let_ t in bind x \x ->
                        letp ("let " <> x <> " : " <> pa <> " := " <> pt <> "; " <> tm u)
  Pi "_" a b         -> let pa = sigma a in bind "_" \_ ->
                        pip (pa <> " → " <> pi b)
  Pi n a b           -> let pa = pair a in bind n \n ->
                        pip (piBind n pa  <> goLinesPis b)
  App t u            -> appp (app t <> " " <> proj u)
  Lam x t            -> letp (bind x \x -> "λ " <> x <> goLams t)
  Line "_" a         -> bindI "_" \_ -> pip ("I → " <> pi a)
  Line x a           -> bindI x   \x -> pip (lineBind x <> goLinesPis a)
  LApp t u           -> appp (app t <> " " <> int u)
  LLam x t           -> letp (bindI x \x -> "λ " <> x <> goLams t)
  Sg "_" a b         -> let pa = eq a in bind "_" \_ ->
                        sigmap (pa <> " × " <> sigma b)
  Sg x a b           -> let pa = pair a in bind x \x ->
                        sigmap ("(" <> x <> " : " <> pa <> ") × " <> sigma b)
  Pair x t u         -> pairp (let_ t <> ", " <> pair u)
  Proj1 t x          -> case unProject t x of
                          Nothing -> projp (proj t <> ".1")
                          Just t  -> projp (proj t <> "." <> str x)
  Proj2 t x          -> projp (proj t <> ".2")
  U                  -> "U"
  Path "_" a t u     -> ifVerbose
                         (let pt = trans t; pu = trans u in bindI "_" \_ ->
                          eqp (pt <> " ={" <> "_" <> ". " <> pair a <> "} " <> pu))
                         (eqp (trans t <> " = " <> trans u))
  Path x a t u       -> let pt = trans t; pu = trans u in bindI x \x ->
                        eqp (pt <> " ={" <> x <> ". " <> pair a <> "} " <> pu)
  PApp l r t u       -> ifVerbose
                          (appp (app t <> " {" <> pair l <> "} {" <> pair r <> "} " <> int u))
                          (appp (app t <> " " <> int u))
  PLam l r x t       -> ifVerbose
                          (let pl = pair l; pr = pair r in
                           letp (bindI x \x -> "λ {" <> pl <> "} {" <> pr <> "} " <> x <> goLams t))
                          (letp (bindI x \x -> "λ " <> x <> goLams t))
  Coe r r' i a t     -> let pt = proj t; pr = int r; pr' = int r' in bindI i \i ->
                        appp ("coe " <> pr <> " " <> pr' <> coeTy i a <> pt)
  HCom r r' a t u    -> appp ("hcom " <> int r <> " " <> int r'
                              <> ifVerbose (" " <> proj a) mempty
                              <> " " <> sysH t <> " " <> proj u)
  GlueTy a s         -> appp ("Glue " <> proj a <> " " <> sys s)
  Unglue t _         -> appp ("unglue " <> proj t)
  Glue a s1 s2       -> ifVerbose
                          (appp ("glue " <> proj a <> " " <> sys s1 <> " " <> sys s2))
                          (appp ("glue " <> proj a <> " " <> sys s2))
  Hole h             -> case h of
                          SrcHole i p -> case i of
                            Just x -> "?" <> str x
                            _      -> runIO $ (getState <&> (^.printingOpts.errPrinting)) >>= \case
                              True -> pure ("?" <> str (sourcePosPretty (coerce p :: SourcePos)))
                              _    -> ifVerbose
                                (pure ("?" <> str (sourcePosPretty (coerce p :: SourcePos))))
                                (pure "?")
                          ErrHole msg ->
                            "(ERR " <> str msg <> ")"
  Com r r' i a t u   -> appp (let pr = int r; pr' = int r'; pt = sysH t; pu = proj u in bindI i \i ->
                        "com " <> pr <> " " <> pr' <> " (" <> i <> ". " <> pair a <> ") "
                               <> pt <> " " <> pu)
  WkI t              -> wkI (tm t)
  Refl _             -> "refl"
  Sym _ _ _ p        -> projp (proj p <> "⁻¹")
  Trans _ _ _ _ p q  -> transp (app p <> " ∙ " <> trans q)
  Ap f _ _ p         -> appp ("ap " <> proj f <> " " <> proj p)
  TyCon inf SPNil    -> topName (^.name) (^.tyId) inf
  TyCon inf ts       -> appp (topName (^.name) (^.tyId) inf <> spine ts)
  DCon inf SPNil     -> dcon inf
  DCon inf sp        -> appp (dcon inf <> spine sp)
  Case t x b _ cs    -> ifVerbose
                         (let pt = proj t; pcs = cases cs in bind x \x ->
                          appp ("case " <> pt <> " (" <> x <> ". " <> tm b <> ") [" <> pcs <> "]"))
                         (appp ("case " <> proj t <> " [" <> cases cs <> "]"))
  Wrap x a           -> "(" <> str x <> " : " <> pair a <> ")"
  Pack x t           -> tm t
  Unpack t x         -> case unProject t x of
                          Nothing -> projp (proj t <> ".1")
                          Just t  -> projp (proj t <> "." <> str x)
  Split x b _ cs     -> appp ("λ[" <> cases cs <> "]")
  HTyCon inf SPNil   -> topName (^.name) (^.tyId) inf
  HTyCon inf ts      -> appp (topName (^.name) (^.tyId) inf <> spine ts)
  HDCon inf _ fs s   -> case fs of
                          SPNil | cod s == 0 -> hdcon inf
                          _ -> appp (hdcon inf <> spine fs <> goSub s)
  HCase t x b _ cs   -> ifVerbose
                         (let pt = proj t; pcs = hcases cs in bind x \x ->
                          appp ("case " <> pt <> " (" <> x <> ". " <> tm b <> ") [" <> pcs <> "]"))
                         (appp ("case " <> proj t <> " [" <> hcases cs <> "]"))
  HSplit x b _ cs    -> appp ("λ[" <> hcases cs <> "]")

----------------------------------------------------------------------------------------------------

dataFields :: PrettyArgs (Tel -> Txt)
dataFields = \case
  TNil         -> mempty
  TCons x a fs -> let pa = pair a in bind x \x ->
                  "(" <> x <> " : " <> pa <> ")" <> dataFields fs

dataCons :: PrettyArgs ([DConInfo] -> Txt)
dataCons = \case
  []     -> mempty
  [inf]  -> str (inf^.name) <> dataFields (inf^.fieldTypes)
  inf:cs -> str (inf^.name) <> dataFields (inf^.fieldTypes) <> "\n  | " <> dataCons cs

hdataIFields :: PrettyArgs (HDConInfo -> [Name] -> Txt)
hdataIFields inf = \case
  []   -> ": I)" <> boundary_ (inf^.boundary)
  i:is -> bindI i \_ -> str i <> " " <> hdataIFields inf is

boundary_ :: PrettyArgs (Sys -> Txt)
boundary_ = \case
  SEmpty -> ";"
  bnd    -> sys bnd

hdataFields :: PrettyArgs (HDConInfo -> Tel -> Txt)
hdataFields inf = \case
  TNil         -> case inf^.ifields of
                    []  -> boundary_ (inf^.boundary)
                    is  -> "(" <> hdataIFields inf is
  TCons x a fs -> let pa = pair a in bind x \x ->
                  "(" <> x <> " : " <> pa <> ")" <> hdataFields inf fs

hdataCon :: PrettyArgs (HDConInfo -> Txt)
hdataCon inf = str (inf^.name) <> hdataFields inf (inf^.fieldTypes)

hdataCons :: PrettyArgs ([HDConInfo] -> Txt)
hdataCons = \case
  []     -> mempty
  [inf]  -> hdataCon inf
  inf:cs -> hdataCon inf <> "\n  | " <> hdataCons cs

inductive :: PrettyArgs (Tel -> [DConInfo] -> Txt)
inductive ps cs = case ps of
  TNil         -> " :=\n    " <> dataCons cs
  TCons x a ps -> let pa = pair a in bind x \x ->
                  " (" <> x <> " : " <> pa <> ")" <> inductive ps cs

hinductive :: PrettyArgs (Tel -> [HDConInfo] -> Txt)
hinductive ps cs = case ps of
  TNil         -> " :=\n    " <> hdataCons cs
  TCons x a ps -> let pa = pair a in bind x \x ->
                  " (" <> x <> " : " <> pa <> ")" <> hinductive ps cs

topEntries :: LM.Map TopEntry -> Txt
topEntries = LM.foldrWithKey'
  (\l e acc -> case e of
      TEDef inf -> withPrettyArgs0 $
         "\n" <> str (inf^.name)
          <> " : " <> pair (inf^.defTy)
          <> " :=\n  " <> pair (inf^.def) <> ";\n" <> acc
          -- <> " :=\n  " <> str (show (inf^.def)) <> ";\n" <> acc
      TETyCon inf -> withPrettyArgs0 $ runIO do
        cons <- readIORef (inf^.constructors)
        pure $!
         "\ninductive " <> str (inf^.name)
         <> inductive (inf^.paramTypes) (LM.elems cons) <> ";\n" <> acc

      TEHTyCon inf -> withPrettyArgs0 $ runIO do
        cons <- readIORef (inf^.constructors)
        pure $!
         "\nhigher inductive " <> str (inf^.name)
         <> hinductive (inf^.paramTypes) (LM.elems cons) <> ";\n" <> acc

      TEHDCon{} -> impossible
      TEDCon{}  -> impossible
      TERec{}   -> impossible)
  mempty

----------------------------------------------------------------------------------------------------

withPrettyArgs0 :: PrettyArgs a -> a
withPrettyArgs0 act = let ?dom = 0; ?idom = 0; ?names = NNil in act

class Pretty c a | a -> c  where
  pretty    :: c => a -> String
  pretty0   :: a -> String

instance Pretty () (LM.Map TopEntry) where
  pretty  t   = runTxt (topEntries t)
  pretty0 t   = runTxt (topEntries t)

instance Pretty (NamesArg, DomArg, IDomArg) Tm where
  pretty    t = runTxt (pair t)
  pretty0   t = withPrettyArgs0 $ runTxt (pair t)

instance Pretty (NamesArg, DomArg, IDomArg) Cof where
  pretty    t = runTxt (cof t)
  pretty0   t = withPrettyArgs0 $ runTxt (cof t)

instance Pretty (NamesArg, DomArg, IDomArg) NeCof where
  pretty    t = runTxt (necof t)
  pretty0   t = withPrettyArgs0 $ runTxt (necof t)

instance Pretty (NamesArg, DomArg, IDomArg) Sys where
  pretty  t   = runTxt (sys t)
  pretty0 t   = withPrettyArgs0 $ runTxt (sys t)
