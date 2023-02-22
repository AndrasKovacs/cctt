
module Elaboration (elabTop) where

import Control.Exception
import Text.Megaparsec (SourcePos(..), unPos, initialPos)
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import System.Exit
import Data.List

import Common hiding (debug)
import Core hiding (bindI, bindCof, define, eval, evalCof, evalI, evalf)
import CoreTypes
import Interval
import Quotation
import Substitution

import qualified Common
import qualified Conversion
import qualified Core
import qualified Presyntax as P

import Pretty

-- import Debug.Trace

--------------------------------------------------------------------------------

conv :: Elab (Val -> Val -> IO ())
conv t u = if Conversion.conv t u
  then pure ()
  else err $ CantConvert (quote t) (quote u)

convCof :: Elab (F VCof -> F VCof -> IO ())
convCof c c' = if Conversion.conv (unF c) (unF c')
  then pure ()
  else err CantConvertCof

eval :: NCofArg => DomArg => EnvArg => Tm -> Val
eval t = let ?sub = idSub (dom ?cof) in Core.eval t

evalf :: NCofArg => DomArg => EnvArg => Tm -> F Val
evalf t = let ?sub = idSub (dom ?cof) in frc (Core.eval t)

evalTopSub :: NCofArg => DomArg => EnvArg => Tm -> F I -> Val
evalTopSub t i = let ?sub = idSub (dom ?cof) `ext` unF i in Core.eval t

evalCof :: NCofArg => Cof -> F VCof
evalCof cof = let ?sub = idSub (dom ?cof) in Core.evalCof cof

evalI :: NCofArg => I -> F I
evalI i = let ?sub = idSub (dom ?cof) in Core.evalI i

evalInf :: NCofArg => I -> I
evalInf i = let ?sub = idSub (dom ?cof) in unF (Core.evalI i)

debug :: (TopNames => Names => INames => [String]) -> Elab (IO ())
debug x = withNames (Common.debug x)

-- Context
--------------------------------------------------------------------------------

data Entry
  = Top Lvl VTy ~Val      -- level, type, value
  | Local Lvl VTy         -- level, type
  | LocalInt IVar
  deriving Show

type Table = M.Map Name Entry

type TableArg = (?tbl    :: Table)
type PosArg   = (?srcPos :: SourcePos)

type Elab a = NCofArg => DomArg => EnvArg => TableArg => PosArg => a

-- | Bind a fibrant variable.
bind :: Name -> VTy -> Elab (Val -> a) -> Elab a
bind x a act =
  let v    = vVar ?dom in
  let ?dom = ?dom + 1
      ?env = EDef ?env v
      ?tbl = M.insert x (Local ?dom a) ?tbl in
  let _ = ?dom; _ = ?env; _ = ?tbl in
  act v
{-# inline bind #-}

-- | Define a fibrant variable.
define :: Name -> VTy -> Val -> Elab a -> Elab a
define x a ~v act =
  let ?env = EDef ?env v
      ?tbl = M.insert x (Local ?dom a) ?tbl in
  let _ = ?env; _ = ?tbl in
  act
{-# inline define #-}

-- | Bind an ivar.
bindI :: Name -> Elab (IVar -> a) -> Elab a
bindI x act =
  let fresh = dom ?cof in
  let ?cof  = setDom (fresh + 1) ?cof `ext` IVar fresh
      ?tbl  = M.insert x (LocalInt fresh) ?tbl in
  let _ = ?cof; _ = ?tbl in
  act fresh
{-# inline bindI #-}

-- | Extend cxt with a cof (by conjunction)
bindVCof :: F VCof -> Elab a -> Elab a
bindVCof cof act =
  let ?cof = conjVCof ?cof cof
  in seq ?cof act
{-# inline bindVCof #-}

-- Errors
--------------------------------------------------------------------------------

data Error
  = NameNotInScope Name
  | UnexpectedI
  | ExpectedI
  | ExpectedPi
  | ExpectedSg
  | ExpectedGlueTy
  | CantInferLam
  | CantInferPair
  | CantInferGlueTm
  | CantConvert Tm Tm
  | CantConvertCof
  | GlueTmSystemMismatch
  | TopShadowing
  deriving Show

instance Exception Error where

data ErrInCxt where
  ErrInCxt :: (TableArg, PosArg) => Error -> ErrInCxt

instance Show ErrInCxt where
  show (ErrInCxt e) = show e

instance Exception ErrInCxt

err :: TableArg => PosArg => Error -> IO a
err e = throwIO $ ErrInCxt e

-- | Convert the symbol table to a printing environment.
withNames :: TableArg => (TopNames => Names => INames => a) -> a
withNames act =
  let go (!top, !ns, !ins) n = \case
        Top x _ _  -> let x' :: Int = fromIntegral x in ((x',n):top, ns, ins)
        Local x _  -> (top, (x,n):ns, ins)
        LocalInt x -> (top, ns, (x,n):ins)
      (top, ns, ins) = M.foldlWithKey' go ([], [], []) ?tbl in

  let ?top    = IM.fromList top
      ?names  = map snd $ sortBy (\(x, _) (y, _) -> compare y x) ns
      ?inames = map snd $ sortBy (\(x, _) (y, _) -> compare y x) ins in
  act
{-# inline withNames #-}

displayErrInCxt :: String -> ErrInCxt -> IO ()
displayErrInCxt file (ErrInCxt e) = withNames do

  let SourcePos path (unPos -> linum) (unPos -> colnum) = ?srcPos
      lnum = show linum
      lpad = map (const ' ') lnum
      msg  = case e of
        CantConvert t u ->
          ("Cannot convert expected type\n\n" ++
           "  " ++ showTm u ++ "\n\n" ++
           "and inferred type\n\n" ++
           "  " ++ showTm t)
        NameNotInScope x ->
           "Name not in scope: " ++ x
        TopShadowing ->
           "Duplicate top-level name"
        e -> show e

  putStrLn (show path ++ ":" ++ lnum ++ ":" ++ show colnum)
  putStrLn (lpad ++ " |")
  putStrLn (lnum ++ " | " ++ (lines file !! (linum - 1)))
  putStrLn (lpad ++ " | " ++ replicate (colnum - 1) ' ' ++ "^")
  putStrLn msg
  putStrLn ""

--------------------------------------------------------------------------------

setPos :: DontShow SourcePos -> (PosArg => a) -> a
setPos pos act = let ?srcPos = coerce pos in act; {-# inline setPos #-}

data Infer = Infer Tm ~VTy

check :: Elab (P.Tm -> VTy -> IO Tm)
check t topA = case t of

  P.Pos pos t ->
    setPos pos $ check t topA

  P.Let x Nothing t u -> do
    Infer t a <- infer t
    let ~vt = eval t
    define x a vt $ check u topA

  P.Let x (Just a) t u -> do
    a <- check a VU
    let va = eval a
    t <- check t va
    let ~vt = eval t
    define x va vt $ check u topA

  t -> case (t, unF (frc topA)) of

    (P.Lam x t, VPi a b) -> do
      Lam x <$!> bind x a (\v -> check t (capp b v))

    (P.Lam x t, VPathP a l r) -> do
      debug ["PLAM CHECK START"]
      t <- bindI x \r -> check t (icapp a (IVar r))
      bindI x \r -> debug ["PLAM body", showTm t, showTm (quote (icapp a (IVar r)))]
      debug ["PLAM sides", showTm (quote l), showTm (quote r)]
      -- debug [show (evalTopSub t (F I0)), show l]
      conv (evalTopSub t (F I0)) l
      debug ["foo"]
      debug ["ELLLL", show (evalTopSub t (F I1)), show r]
      conv (evalTopSub t (F I1)) r -- PROBLEMO
      debug ["bar"]
      pure $! PLam (quote l) (quote r) x t

    (P.Pair t u, VSg a b) -> do
      t <- check t a
      u <- check u (b ∙ eval t)
      pure $! Pair t u

    (P.GlueTm base ts, VGlueTy a equivs _) -> do
      base <- check base a
      ts   <- elabGlueTmSys base ts a equivs
      pure $ Glue base ts

    (t, topA) -> do
      Infer t a <- infer t
      conv a topA
      pure t

infer :: Elab (P.Tm -> IO Infer)
infer = \case
  P.Ident x -> case M.lookup x ?tbl of
    Nothing -> err $ NameNotInScope x
    Just e  -> case e of
      Top l a v  -> pure $! Infer (TopVar l (DontShow v)) a
      Local l a  -> pure $! Infer (LocalVar (lvlToIx ?dom l)) a
      LocalInt l -> err UnexpectedI

  P.I0 -> err UnexpectedI
  P.I1 -> err UnexpectedI

  P.PathP x a t u -> do
    a <- bindI x \_ -> check a VU
    t <- check t (evalTopSub a (F I0))
    u <- check u (evalTopSub a (F I1))
    pure $! Infer (PathP x a t u) VU

  P.Pos pos t ->
    setPos pos $ infer t

  P.Let x Nothing t u -> do
    Infer t a <- infer t
    let ~vt = eval t
    define x a vt $ infer u

  P.Let x (Just a) t u -> do
    a <- check a VU
    let va = eval a
    t <- check t va
    let ~vt = eval t
    define x va vt $ infer u

  P.Pi x a b -> do
    a <- check a VU
    b <- bind x (eval a) \_ -> check b VU
    pure $ Infer (Pi x a b) VU

  P.App t u -> do
    Infer t a <- infer t
    case unF (frc a) of
      VPi a b -> do
        u <- check u a
        pure $! Infer (App t u) (b ∙ eval u)
      VPathP a l r -> do
        u <- checkI u
        pure $! Infer (PApp (quote l) (quote r) t u) (a ∙ evalInf u)
      _ ->
        err ExpectedPi

  P.Lam{} ->
    err CantInferLam

  P.Sg x a b -> do
    a <- check a VU
    b <- bind x (eval a) \_ -> check b VU
    pure $ Infer (Sg x a b) VU

  P.Pair{} ->
    err CantInferPair

  P.Proj1 t -> do
    Infer t a <- infer t
    case unF (frc a) of
      VSg a b -> pure $ Infer (Proj1 t) a
      _       -> err ExpectedSg

  P.Proj2 t -> do
    Infer t a <- infer t
    case unF (frc a) of
      VSg a b -> pure $! Infer (Proj2 t) (b ∙ proj1 (evalf t))
      _       -> err ExpectedSg

  P.U ->
    pure $ Infer U VU

  P.Path t u -> do
    Infer t a <- infer t
    u <- check u a
    pure $ Infer (PathP "_" (Core.freshI \_ -> quote a) t u) VU

  P.Coe r r' x a t -> do --
    r  <- checkI r
    r' <- checkI r'
    a  <- bindI x \_ -> check a VU
    t  <- check t (evalTopSub a (evalI r))
    pure $! Infer (Coe r r' x a t) (evalTopSub a (evalI r'))

  P.HCom r r' Nothing sys t -> do
    r  <- checkI r
    r' <- checkI r'
    Infer t a <- infer t
    sys <- elabSysHCom a r t sys
    pure $! Infer (HCom r r' (quote a) sys t) a

  P.HCom r r' (Just a) sys t -> do
    r   <- checkI r
    r'  <- checkI r'
    a   <- check a VU
    let va = eval a
    t   <- check t va
    sys <- elabSysHCom va r t sys
    pure $! Infer (HCom r r' a sys t) va

  P.GlueTy a sys -> do
    a   <- check a VU
    sys <- elabGlueTySys (eval a) sys
    pure $! Infer (GlueTy a sys) VU

  P.GlueTm _ _ -> do
    err CantInferGlueTm

  P.Unglue t -> do
    Infer t a <- infer t
    case unF (frc a) of
      VGlueTy a sys _ -> pure $! Infer (Unglue t (quote sys)) a
      _               -> err ExpectedGlueTy

  P.Nat ->
    pure $! Infer Nat VU

  P.Zero ->
    pure $! Infer Zero VNat

  P.Suc t -> do
    t <- check t VNat
    pure $! Infer (Suc t) VNat

  -- NatElim : (P : Nat -> U) -> P z -> ((n:_) -> P n -> P (suc n)) -> (n:_) -> P n
  P.NatElim p s z n -> do
    p <- check p (fun VNat VU)
    let vp = evalf p
    s <- check s (VPi VNat $ NCl "n" $ CNatElim (unF vp))
    z <- check z (vp ∙ VZero)
    n <- check n VNat
    pure $! Infer (NatElim p s z n) (vp ∙~ eval n)

checkI :: Elab (P.Tm -> IO I)
checkI = \case
  P.Pos pos t ->
    setPos pos $ checkI t

  P.I0 -> pure I0
  P.I1 -> pure I1

  P.Ident x -> do
    case M.lookup x ?tbl of
      Nothing           -> err $ NameNotInScope x
      Just (LocalInt l) -> pure $ IVar l
      Just _            -> err ExpectedI

  t -> do
    err ExpectedI

--------------------------------------------------------------------------------

checkCofEq :: Elab (P.CofEq -> IO CofEq)
checkCofEq (P.CofEq t u) = CofEq <$!> checkI t <*!> checkI u

checkCof :: Elab (P.Cof -> IO Cof)
checkCof = \case
  P.CTrue       -> pure CTrue
  P.CAnd eq cof -> CAnd <$!> checkCofEq eq <*!> checkCof cof

------------------------------------------------------------

goSysCompatHCom :: Elab (Tm -> SysHCom -> IO ())
goSysCompatHCom t = \case
  SHEmpty              -> pure ()
  SHCons cof' x t' sys -> do
    case unF (evalCof cof') of
      VCFalse     -> pure ()
      (F -> cof') -> bindVCof cof' $ bindI x \_ -> conv (eval t) (eval t')
    goSysCompatHCom t sys

sysCompatHCom :: Elab (F VCof -> Tm -> SysHCom -> IO ())
sysCompatHCom cof t sys = bindVCof cof $ goSysCompatHCom t sys

elabSysHCom :: Elab (VTy -> I -> Tm ->  P.SysHCom -> IO SysHCom)
elabSysHCom a r base = \case
  P.SHEmpty ->
    pure SHEmpty
  P.SHCons cof x t sys -> do
    cof <- checkCof cof
    let vcof = evalCof cof

    t <- bindVCof vcof do
      t <- bindI x \_ -> check t a
      conv (evalTopSub t (frc r)) (eval base) -- check base boundary
      pure t

    sys <- elabSysHCom a r base sys
    sysCompatHCom vcof t sys -- check system compatibility
    pure $ SHCons cof x t sys

------------------------------------------------------------

elabGlueTmSys :: Elab (Tm -> P.Sys -> VTy -> NeSys -> IO Sys)
elabGlueTmSys base ts a equivs = case (ts, equivs) of
  (P.SEmpty, NSEmpty) ->
    pure SEmpty

  (P.SCons cof t ts, NSCons (BindCofLazy cof' equiv) equivs) -> do
    cof <- checkCof cof
    let vcof = evalCof cof
    convCof vcof (frc cof')

    t <- bindVCof vcof do
      let fequiv = frc equiv
      t <- check t (proj1 fequiv)
      conv (proj1f (proj2f fequiv) ∙ eval t) (eval base)
      pure t

    ts <- elabGlueTmSys base ts a equivs
    sysCompat vcof t ts
    pure $ SCons cof t ts

  (_, _) ->
    err GlueTmSystemMismatch

------------------------------------------------------------

goSysCompat :: Elab (Tm -> Sys -> IO ())
goSysCompat t = \case
  SEmpty            -> pure ()
  SCons cof' t' sys -> do
    case unF (evalCof cof') of
      VCFalse     -> pure ()
      (F -> cof') -> bindVCof cof' $ conv (eval t) (eval t')
    goSysCompat t sys

sysCompat :: Elab (F VCof -> Tm -> Sys -> IO ())
sysCompat cof t sys = bindVCof cof $ goSysCompat t sys

elabGlueTySys :: Elab (VTy -> P.Sys -> IO Sys)
elabGlueTySys a = \case
  P.SEmpty ->
    pure SEmpty
  P.SCons cof t sys -> do
    cof <- checkCof cof
    let vcof = evalCof cof
    t <- bindVCof vcof $ check t (equivInto a)
    sys <- elabGlueTySys a sys
    sysCompat vcof t sys
    pure $ SCons cof t sys


------------------------------------------------------------

type ElabTop a = (?topLvl :: Lvl) => Elab a

defineTop :: Name -> VTy -> Val -> ElabTop a -> ElabTop a
defineTop x a ~v act =
  let ?topLvl = ?topLvl + 1
      ?tbl    = M.insert x (Top ?topLvl a v) ?tbl in
  let _ = ?topLvl; _ = ?tbl in
  act
{-# inline defineTop #-}

noTopShadowing :: ElabTop (Name -> IO ())
noTopShadowing x = case M.lookup x ?tbl of
  Just{} -> err TopShadowing
  _      -> pure ()

inferTop :: ElabTop (P.Top -> IO Top)
inferTop = \case

  P.TDef pos x ma t top -> setPos pos do
    noTopShadowing x
    (a, va, t) <- case ma of
      Nothing -> do
        Infer t va <- infer t
        pure (quote va, va, t)
      Just a -> do
        a <- check a VU
        let ~va = eval a
        t <- check t va
        pure (a, va, t)

    let ~vt = eval t
    withNames $ debug ["TOPNF", x, show t, showTm (quote vt)]
    top <- defineTop x va vt $ inferTop top
    pure $! TDef x a t top

  P.TEmpty ->
    pure TEmpty

elabTop :: FilePath -> String -> P.Top -> IO Top
elabTop path file top = do
  let ?cof    = idSub 0
      ?dom    = 0
      ?env    = ENil
      ?tbl    = mempty
      ?srcPos = initialPos path
      ?topLvl = 0
  catch (inferTop top) \(e :: ErrInCxt) -> do
    displayErrInCxt file e
    exitSuccess
