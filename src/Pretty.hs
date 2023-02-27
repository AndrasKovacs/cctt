
module Pretty (
    type TopNames
  , type Names
  , type INames
  , Pretty(..)) where

import Prelude hiding (pi)
import Data.String
import qualified Data.IntMap as M

import Common
import CoreTypes
import Interval

-- import Debug.Trace

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

type Prec     = (?prec   :: Int)
type Names    = (?names  :: [Name])
type TopNames = (?top    :: M.IntMap Name)
type INames   = (?inames :: [Name])

par :: Prec => Int -> Txt -> Txt
par p s | p < ?prec = char '(' <> s <> char ')'
        | True      = s
{-# inline par #-}

projp  s = par 6 s; {-# inline projp #-}
appp   s = par 5 s; {-# inline appp #-}
eqp    s = par 4 s; {-# inline eqp #-}
sigmap s = par 3 s; {-# inline sigmap #-}
pip    s = par 2 s; {-# inline pip #-}
letp   s = par 1 s; {-# inline letp #-}
pairp  s = par 0 s; {-# inline pairp #-}

--------------------------------------------------------------------------------

count :: [Name] -> Name -> Int
count ns n = go ns 0 where
  go []      acc = acc
  go (n':ns) acc | n == n' = go ns (acc + 1)
                 | True    = go ns acc

freshen :: [Name] -> Name -> Name
freshen ns x = case count ns x of
  0 -> x
  n -> x ++ show n

var :: [Name] -> Ix -> Txt
var ns topIx = Txt (go ns topIx) where
  go (n:ns) 0 acc = case n of "_" -> '@': (show topIx ++ acc)
                              n   -> freshen ns n ++ acc
  go (n:ns) x acc = go ns (x - 1) acc
  go _      _ acc = "(INVALID " ++ show topIx ++ ")" ++ acc

fresh :: Name -> (Names => Txt -> a) -> Names => a
fresh x act = let x' = freshen ?names x in
              let ?names = x : ?names in
              act (str x')
{-# inline fresh #-}

freshI :: Name -> (INames => Txt -> a) -> INames => a
freshI x act = let x' = freshen ?inames x in
              let ?inames = x : ?inames in
              act (str x')
{-# inline freshI #-}

wkI :: (INames => a) -> INames => a
wkI act = let ?inames = tail ?inames in act
{-# inline wkI #-}

proj  x = doTm 6 x; {-# inline proj #-}
app   x = doTm 5 x; {-# inline app #-}
eq    x = doTm 4 x; {-# inline eq #-}
sigma x = doTm 3 x; {-# inline sigma #-}
pi    x = doTm 2 x; {-# inline pi #-}
let_  x = doTm 1 x; {-# inline let_ #-}
pair  x = doTm 0 x; {-# inline pair #-}

doTm :: TopNames => Names => INames => Int -> Tm -> Txt
doTm p t = let ?prec = p in tm t; {-# inline doTm #-}

piBind :: Txt -> Txt -> Txt
piBind n a = "(" <> n <> " : " <> a <> ")"; {-# inline piBind #-}

lineBind :: Txt -> Txt
lineBind n = "(" <> n <> " : I)"; {-# inline lineBind #-}

goLinesPis :: TopNames => Names => INames => Tm -> Txt
goLinesPis = \case
  Pi x a b | x /= "_" ->
    let pa = pair a in fresh x \x ->
    piBind x pa <> goLinesPis b
  Line x b | x /= "_" ->
    freshI x \x -> lineBind x <> goLinesPis b
  t ->
    " → " <> pi t

goLams :: TopNames => Names => INames => Tm -> Txt
goLams = \case
  Lam x t      -> fresh  x \x -> " " <> x <> goLams t
  PLam _ _ x t -> freshI x \x -> " " <> x <> goLams t
  LLam x t     -> freshI x \x -> " " <> x <> goLams t
  t            -> ". " <> let_ t

int :: INames => I -> Txt
int = \case
  I0     -> "0"
  I1     -> "1"
  IVar x -> var ?inames (lvlToIx (fromIntegral (length ?inames)) (coerce x))

cofEq :: INames => CofEq -> Txt
cofEq (CofEq i j) = int i <> " = " <> int j

cof :: INames => Cof -> Txt
cof = \case
  CTrue         -> "⊤"
  CAnd eq CTrue -> cofEq eq
  CAnd eq c     -> cofEq eq <> " ∧ " <> cof c

goSysH :: TopNames => Names => INames => SysHCom -> Txt
goSysH = \case
  SHEmpty              -> mempty
  SHCons c x t SHEmpty -> let pc = cof c in freshI x \x ->
                          pc <> " " <> x <> ". " <> pair t
  SHCons c x t sys     -> let pc = cof c; psys = goSysH sys in freshI x \x ->
                          pc <> " " <> x <> ". " <> pair t <> "; " <> psys

sysH :: TopNames => Names => INames => SysHCom -> Txt
sysH s = "[" <> goSysH s <> "]"

goSys :: TopNames => Names => INames => Sys -> Txt
goSys = \case
  SEmpty           -> mempty
  SCons c t SEmpty -> cof c <> ". " <> pair t
  SCons c t sys    -> cof c <> ". " <> pair t <> "; " <> goSys sys

sys :: TopNames => Names => INames => Sys -> Txt
sys s = "[" <> goSys s <> "]"

tm :: TopNames => Names => INames => Prec => Tm -> Txt
tm = \case
  TopVar x _       -> str (?top M.! fromIntegral x)
  LocalVar x       -> var ?names x
  Let x a t u      -> let pa = let_ a; pt = let_ t in fresh x \x ->
                      letp ("let " <> x <> " : " <> pa <> " := " <> pt <> "; " <> tm u)

  Pi "_" a b       -> let pa = sigma a in fresh "_" \_ ->
                      pip (pa <> " → " <> pi b)
  Pi n a b         -> let pa = pair a in fresh n \n ->
                      pip (piBind n pa  <> goLinesPis b)
  App t u          -> appp (app t <> " " <> proj u)
  Lam x t          -> letp (fresh x \x -> "λ " <> x <> goLams t)

  Line "_" a       -> freshI "_" \_ -> pip ("I → " <> pi a)
  Line x a         -> freshI x   \x -> pip (lineBind x <> goLinesPis a)
  LApp t u         -> appp (app t <> " " <> int u)
  LLam x t         -> letp (freshI x \x -> "λ " <> x <> goLams t)

  Sg "_" a b       -> let pa = eq a in fresh "_" \_ ->
                      sigmap (pa <> " × " <> sigma b)
  Sg x a b         -> let pa = pair a in fresh x \x ->
                      sigmap ("(" <> x <> " : " <> pa <> ") × " <> sigma b)
  Pair t u         -> pairp (let_ t <> ", " <> pair u)
  Proj1 t          -> projp (proj t <> ".1")
  Proj2 t          -> projp (proj t <> ".2")

  U                -> "U"

  Path "_" _ t u   -> eqp (app t <> " = " <> app u)
  Path x a t u     -> let pt = app t; pu = app u in freshI x \x ->
                      eqp (pt <> " ={" <> x <> ". " <> pair a <> "} " <> pu)
  PApp l r t u     -> appp (app t <> " " <> app l <> " " <> app r <> " " <> int u)
  PLam _ _ x t     -> letp (freshI x \x -> "λ " <> x <> goLams t)

  Coe r r' i a t   -> let pt = proj t; pr = int r; pr' = int r' in freshI i \i ->
                      appp ("coe " <> pr <> " " <> pr' <> " (" <> i <> ". " <> pair a <> ") " <> pt)
  HCom r r' _ t u  -> appp ("hcom " <> int r <> " " <> int r' <> " " <> sysH t <> " " <> proj u)
  GlueTy a s       -> appp ("Glue " <> proj a <> " " <> sys s)
  Unglue t _       -> appp ("unglue " <> proj t)
  Glue a s         -> appp ("glue " <> proj a <> " " <> sys s)
  Nat              -> "Nat"
  Zero             -> "zero"
  Suc t            -> appp ("suc " <> proj t)
  NatElim p s z n  -> appp ("NatElim " <> proj p <> " " <> proj s <> " " <> proj z <> " " <> proj n)
  TODO             -> "TODO"
  Com r r' i a t u -> appp (let pr = int r; pr' = int r'; pt = sysH t; pu = proj u in freshI i \i ->
                      "com " <> pr <> " " <> pr' <> " (" <> i <> ". " <> pair a <> ") "
                             <> pt <> " " <> pu)
  WkI t            -> wkI (tm t)

top :: TopNames => LvlArg => Top -> Txt
top = \case
  TEmpty       -> mempty
  TDef x a t u ->
    let ?names = []; ?inames = [] in
    "\n" <> str x <> " : " <> pair a <> "\n  := " <> pair t <> ";\n" <>
    (let ?top = M.insert (fromIntegral ?lvl) x ?top
         ?lvl = ?lvl + 1 in
     top u)

----------------------------------------------------------------------------------------------------

class Pretty c c0 a | a -> c c0 where
  pretty  :: c => a -> String
  pretty0 :: c0 => a -> String

instance Pretty () () Top where
  pretty  t = let ?top = mempty; ?lvl = 0 in runTxt (top t)
  pretty0 t = let ?top = mempty; ?lvl = 0 in runTxt (top t)

instance Pretty (TopNames, Names, INames) TopNames Tm where
  pretty  t = runTxt (pair t)
  pretty0 t = let ?names = []; ?inames = [] in runTxt (pair t)

instance Pretty INames () Cof where
  pretty  = runTxt . cof
  pretty0 c = let ?inames = [] in runTxt (cof c)

instance Pretty (TopNames, Names, INames) TopNames Sys where
  pretty  s = runTxt (sys s)
  pretty0 s = let ?names = []; ?inames = [] in runTxt (sys s)
