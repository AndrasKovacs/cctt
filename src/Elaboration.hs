{-# options_ghc -Wno-unused-imports #-}

module Elaboration where

import qualified Data.Map.Strict as M
import Text.Megaparsec (SourcePos)
import Control.Exception

import Common
import Conversion hiding (conv, convCof)
import Core hiding (bind, bindI, bindCof)
import Interval
import Substitution

import qualified IVarSet   as IS
import qualified Presyntax as P
import qualified Core
import qualified Conversion

-- Context
--------------------------------------------------------------------------------

data Entry
  = Top Lvl VTy ~Val      -- level, type, value
  | Local Lvl VTy         -- level, type
  | LocalInt IVar

type TableArg = (?tbl    :: M.Map Name Entry)
type PosArg   = (?srcPos :: SourcePos)

type Elab a = IDomArg => SubArg => NCofArg => DomArg => EnvArg => TableArg => PosArg => a

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
  let fresh = ?idom in
  let ?idom = ?idom + 1
      ?sub  = extSub ?sub (IVar ?idom)
      ?cof  = extSub ?cof (IVar ?idom)
      ?tbl  = M.insert x (LocalInt fresh) ?tbl in
  act fresh
{-# inline bindI #-}

-- | Extend cxt with a cof (by conjunction)
bindCof :: Cof -> Elab a -> Elab a
bindCof cof act =
  let ?cof = conjVCof ?cof (evalCof cof)
  in seq ?cof act
{-# inline bindCof #-}

-- | Extend cxt with a cof (by conjunction)
bindVCof :: F VCof -> Elab a -> Elab a
bindVCof cof act =
  let ?cof = conjVCof ?cof cof
  in seq ?cof act
{-# inline bindVCof #-}

--------------------------------------------------------------------------------

conv :: Elab (Val -> Val -> IO ())
conv t u = if Conversion.conv t u
  then pure ()
  else err CantConvert

convCof :: Elab (F VCof -> F VCof -> IO ())
convCof c c' = if Conversion.convCof c c'
  then pure ()
  else err CantConvertCof

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
  | CantConvert      -- TODO: add info
  | CantConvertCof
  | GlueTmSystemMismatch
  deriving Show

instance Exception Error where

data ErrInCxt = ErrInCxt SourcePos Error
  deriving Show

instance Exception ErrInCxt where

err :: PosArg => Error -> IO a
err e = throwIO $ ErrInCxt ?srcPos e

--------------------------------------------------------------------------------

data Infer = Infer Tm ~VTy

check :: Elab (P.Tm -> VTy -> IO Tm)
check t topA = case t of

  P.Pos pos t -> do
    let ?srcPos = coerce pos in check t topA

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

  t -> case (t, unF (force topA)) of

    (P.Lam x t, VPi _ a b) -> do
      Lam x <$!> bind x a (\v -> check t (capp b v))

    (P.Lam x t, VPathP _ a l r) -> do
      t <- bindI x \r -> check t (icapp a (IVar r))
      conv (evalTopSub t (F I0)) l
      conv (evalTopSub t (F I1)) r
      pure $! PLam (quote l) (quote r) x t

    (P.Pair t u, VSg x a b) -> do
      t <- check t a
      u <- check u (capp b (eval t))
      pure $! Pair t u

    (P.GlueTm base ts, VGlueTy a equivs) -> do
      base <- check base a
      ts   <- checkGlueTmSys base ts a (_nsys equivs)
      pure $ Glue base ts

    (t, topA) -> do
      Infer t a <- infer t
      conv a topA
      pure t

checkGlueTmSys :: Elab (Tm -> P.System -> VTy -> NSystem VCof -> IO System)
checkGlueTmSys base ts a equivs = case (ts, equivs) of
  (P.SEmpty, NSEmpty) ->
    pure SEmpty
  (P.SCons cof t ts, NSCons (forceCof -> cof') (force -> equiv) equivs) -> do
    cof <- checkCof cof
    let vcof = evalCof cof
    convCof vcof cof'
    let b  = proj1 equiv
        f  = proj1f (proj2f equiv)
    t <- bindVCof vcof do
      t <- check t b
      conv (app f (eval t)) (eval base)
      pure t
    ts <- checkGlueTmSys base ts a equivs
    checkBoundaries vcof t ts
    pure $ SCons cof t ts
  (_, _) ->
    err GlueTmSystemMismatch

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
    let ?srcPos = coerce pos in infer t

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
    case unF (force a) of
      VPi x a b -> do
        u <- check u a
        pure $! Infer (App t u) (capp b (eval u))
      VPathP x a l r -> do
        u <- checkI u
        pure $! Infer (PApp (quote l) (quote r) t u) (icapp a (unF (evalI u)))
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
    case unF (force a) of
      VSg x a b -> do
        pure $ Infer (Proj1 t) a
      _ ->
        err ExpectedSg

  P.Proj2 t -> do
    Infer t a <- infer t
    case unF (force a) of
      VSg x a b -> do
        pure $! Infer (Proj2 t) (capp b (proj1 (evalf t)))
      _ ->
        err ExpectedSg

  P.U ->
    pure $ Infer U VU

  P.Path t u -> do
    Infer t a <- infer t
    u <- check u a
    pure $ Infer (PathP "_" (Core.bindI \_ -> quote a) t u) VU

  P.Coe r r' x a t -> do
    r  <- checkI r
    r' <- checkI r'
    a  <- bindI x \_ -> check a VU
    t  <- check t (evalTopSub a (evalI r))
    pure $! Infer (Coe r r' x a t) (evalTopSub a (evalI r'))

  P.HCom r r' x Nothing sys t -> do
    r  <- checkI r
    r' <- checkI r'
    Infer t a <- infer t
    sys <- checkHComSys r r' x a sys t
    pure $! Infer (HCom r r' x (quote a) sys t) a

  P.HCom r r' x (Just a) sys t -> do
    r   <- checkI r
    r'  <- checkI r'
    a   <- check a VU
    let va = eval a
    t   <- check t va
    sys <- checkHComSys r r' x va sys t
    pure $! Infer (HCom r r' x a sys t) va

  P.GlueTy a sys -> do
    a   <- check a VU
    sys <- elabGlueTySys (eval a) sys
    pure $! Infer (GlueTy a sys) VU

  P.GlueTm _ _ -> do
    err CantInferGlueTm

  P.Unglue t -> do
    Infer t a <- infer t
    case unF (force a) of
      VGlueTy a sys -> do
        let ~qsys = quoteSys (_nsys sys)
        pure $! Infer (Unglue t qsys) a
      _ ->
        err ExpectedGlueTy

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
    s <- check s (VPi "n" VNat (CNatElim (unF vp)))
    z <- check z (vp `app` VZero)
    n <- check n VNat
    pure $! Infer (NatElim p s z n) (vp `appLazy` eval n)

checkI :: Elab (P.Tm -> IO I)
checkI = \case
  P.I0 -> pure I0
  P.I1 -> pure I1

  P.Ident x -> case M.lookup x ?tbl of
    Nothing           -> err (NameNotInScope x)
    Just (LocalInt l) -> pure $ IVar l
    Just _            -> err ExpectedI

  _ -> err ExpectedI

--------------------------------------------------------------------------------

checkCofEq :: Elab (P.CofEq -> IO CofEq)
checkCofEq (P.CofEq t u) = CofEq <$!> checkI t <*!> checkI u

checkCof :: Elab (P.Cof -> IO Cof)
checkCof = \case
  P.CTrue       -> pure CTrue
  P.CAnd eq cof -> CAnd <$!> checkCofEq eq <*!> checkCof cof

goCheckBoundaries :: Elab (Tm -> System -> IO ())
goCheckBoundaries t = \case
  SEmpty            -> pure ()
  SCons cof' t' sys -> do bindCof cof' $ conv (eval t) (eval t')
                          goCheckBoundaries t sys

checkBoundaries :: Elab (F VCof -> Tm -> System -> IO ())
checkBoundaries cof t sys = bindVCof cof $ goCheckBoundaries t sys

-- | Elaborate hcom system, don't yet check base boundary condition.
elabHComSys :: Elab (Name -> VTy -> P.System -> IO System)
elabHComSys x a = \case
  P.SEmpty ->
    pure SEmpty
  P.SCons cof t sys -> do
    cof <- checkCof cof
    let vcof = evalCof cof
    t   <- bindI x \_ -> bindVCof vcof (check t a)
    sys <- elabHComSys x a sys
    -- NOTE: here we implicitly weaken all cofs under the ivar binder
    bindI x \_ -> checkBoundaries vcof t sys
    pure $ SCons cof t sys

checkHComSys :: Elab (I -> I -> Name -> VTy -> P.System -> Tm -> IO System)
checkHComSys r r' x a sys t = do
  sys <- elabHComSys x a sys
  bindI x \v -> checkBoundaries (evalCof (CofEq (IVar v) r `CAnd` CTrue)) t sys
  pure sys

elabGlueTySys :: Elab (VTy -> P.System -> IO System)
elabGlueTySys a = \case
  P.SEmpty ->
    pure SEmpty
  P.SCons cof t sys -> do
    cof <- checkCof cof
    let vcof = evalCof cof
    t   <- bindVCof vcof $ check t (equivInto a)
    sys <- elabGlueTySys a sys
    checkBoundaries vcof t sys
    pure $ SCons cof t sys
