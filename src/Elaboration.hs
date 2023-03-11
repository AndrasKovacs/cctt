{-# options_ghc -Wno-unused-top-binds #-}

module Elaboration (elabTop) where

import Control.Exception
import Text.Megaparsec (SourcePos(..), unPos, initialPos)
import qualified Data.Map.Strict as M
import System.Exit

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

----------------------------------------------------------------------------------------------------

conv :: Elab (Val -> Val -> IO ())
conv t u = if Conversion.conv t u
  then pure ()
  else err $ CantConvert (quote t) (quote u)

convICl :: Elab (NamedIClosure -> NamedIClosure -> IO ())
convICl t u = if Conversion.conv t u
  then pure ()
  else err $ CantConvert (quote t) (quote u)

convExInf :: Elab (Val -> Val -> IO ())
convExInf t u = if Conversion.conv t u
  then pure ()
  else err $ CantConvertExInf (quote t) (quote u)

convNeCof :: Elab (NeCof -> NeCof -> IO ())
convNeCof c c' = if Conversion.conv c c'
  then pure ()
  else err $! CantConvertCof (quote c) (quote c')

convEndpoints :: Elab (Val -> Val -> IO ())
convEndpoints t u = if Conversion.conv t u
  then pure ()
  else err $ CantConvertEndpoints (quote t) (quote u)

eval :: NCofArg => DomArg => EnvArg => Tm -> Val
eval t = let ?sub = idSub (dom ?cof) in Core.eval t

evalf :: NCofArg => DomArg => EnvArg => Tm -> F Val
evalf t = let ?sub = idSub (dom ?cof) in frc (Core.eval t)

instantiate :: NCofArg => DomArg => EnvArg => Tm -> F I -> Val
instantiate t i = let ?sub = idSub (dom ?cof) `ext` unF i in Core.eval t

evalCof :: NCofArg => Cof -> F VCof
evalCof cof = let ?sub = idSub (dom ?cof) in Core.evalCof cof

evalI :: NCofArg => I -> F I
evalI i = let ?sub = idSub (dom ?cof) in Core.evalI i

evalInf :: NCofArg => I -> I
evalInf i = let ?sub = idSub (dom ?cof) in unF (Core.evalI i)

debug :: PrettyArgs [String] -> Elab (IO ())
debug x = withPrettyArgs (Common.debug x)

----------------------------------------------------------------------------------------------------
-- Elaboration context
----------------------------------------------------------------------------------------------------

data Entry
  = Top Lvl VTy ~Val      -- level, type, value
  | Local Lvl VTy         -- level, type
  | LocalInt IVar
  deriving Show

data Box a = Box ~a deriving (Show)

type Table      = M.Map Name Entry
type TableArg   = (?tbl        :: Table)
type PosArg     = (?srcPos     :: SourcePos)
type TopDefs    = (?topDefs    :: [(Val, VTy)])
type TopLvl     = (?topLvl     :: Lvl)
type LocalTypes = (?localTypes :: [Box VTy])

type Elab a = TopDefs => TopLvl => LocalTypes => NCofArg
           => DomArg => EnvArg => TableArg => PosArg => a

-- | Bind a fibrant variable.
bind :: Name -> VTy -> Elab (Val -> a) -> Elab a
bind x ~a act =
  let v           = vVar ?dom in
  let ?dom        = ?dom + 1
      ?env        = EDef ?env v
      ?tbl        = M.insert x (Local ?dom a) ?tbl
      ?localTypes = Box a : ?localTypes in
  let _ = ?dom; _ = ?env; _ = ?tbl in
  act v
{-# inline bind #-}

-- | Define a fibrant variable.
define :: Name -> VTy -> Val -> Elab a -> Elab a
define x ~a ~v act =
  let ?env        = EDef ?env v
      ?dom        = ?dom + 1
      ?tbl        = M.insert x (Local ?dom a) ?tbl
      ?localTypes = Box a : ?localTypes in
  let _ = ?env; _ = ?tbl; _ = ?dom in
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

bindCof :: NeCof' -> Elab a -> Elab a
bindCof (NeCof' cof c) act = let ?cof = cof in act; {-# inline bindCof #-}

-- | Try to pick an informative fresh ivar name.
pickIVarName :: Elab Name
pickIVarName
  | M.notMember "i" ?tbl = "i"
  | M.notMember "j" ?tbl = "j"
  | M.notMember "k" ?tbl = "k"
  | M.notMember "l" ?tbl = "l"
  | M.notMember "m" ?tbl = "m"
  | True                 = "i"

----------------------------------------------------------------------------------------------------
-- Errors
----------------------------------------------------------------------------------------------------

data Error
  = NameNotInScope Name
  | LocalLvlNotInScope
  | TopLvlNotInScope
  | UnexpectedI
  | UnexpectedIType
  | ExpectedI
  | ExpectedPiPathLine Tm
  | ExpectedSg Tm
  | ExpectedGlueTy Tm
  | ExpectedPathLine Tm
  | ExpectedPath Tm
  | ExpectedPathULineU Tm
  | ExpectedNonDepFun Tm
  | CantInferLam
  | CantInferPair
  | CantInfer
  | CantInferGlueTm
  | CantConvert Tm Tm
  | CantConvertCof Cof Cof
  | CantConvertEndpoints Tm Tm
  | CantConvertExInf Tm Tm
  | GlueTmSystemMismatch Sys
  | TopShadowing
  | NonNeutralCofInSystem
  deriving Show

instance Exception Error where

data ErrInCxt where
  ErrInCxt :: (TableArg, PosArg, NCofArg, DomArg) => Error -> ErrInCxt

instance Show ErrInCxt where
  show (ErrInCxt e) = show e

instance Exception ErrInCxt

err :: TableArg => PosArg => NCofArg => DomArg => Error -> IO a
err e = throwIO $ ErrInCxt e

-- | Convert the symbol table to a printing environment.
withPrettyArgs :: TableArg => DomArg => NCofArg => PrettyArgs a -> a
withPrettyArgs act =
  let entryToNameKey = \case
        Top x _ _  -> NKTop x
        Local x _  -> NKLocal x
        LocalInt x -> NKLocalI x in
  let ?idom   = dom ?cof
      ?names  = M.foldlWithKey'
                  (\acc name e -> M.insert (entryToNameKey e) name acc)
                  mempty ?tbl
      ?shadow = mempty in
  act
{-# inline withPrettyArgs #-}

showError :: PrettyArgs (Error -> String)
showError = \case
  CantConvertExInf t u ->
    "Can't convert expected type\n\n" ++
    "  " ++ pretty u ++ "\n\n" ++
    "and inferred type\n\n" ++
    "  " ++ pretty t

  CantInfer ->
    "Can't infer type for expression"

  CantConvert t u ->
    "Can't convert\n\n" ++
    "  " ++ pretty u ++ "\n\n" ++
    "and\n\n" ++
    "  " ++ pretty t

  CantConvertEndpoints t u ->
    "Can't convert expected path endpoint\n\n" ++
    "  " ++ pretty u ++ "\n\n" ++
    "to the inferred endpoint\n\n" ++
    "  " ++ pretty t

  CantConvertCof c1 c2 ->
    "Can't convert expected path endpoint\n\n" ++
    "  " ++ pretty c1 ++ "\n\n" ++
    "to\n\n" ++
    "  " ++ pretty c2

  NameNotInScope x ->
    "Name not in scope: " ++ x

  LocalLvlNotInScope ->
    "Local De Bruijn level not in scope"

  TopLvlNotInScope ->
    "Top-level De Bruijn level not in scope"

  TopShadowing ->
    "Duplicate top-level name"

  UnexpectedI ->
    "Unexpected interval expression"

  ExpectedI ->
    "Expected an interval expression"

  ExpectedPath a ->
    "Expected a path type, inferred\n\n" ++
    "  " ++ pretty a

  ExpectedPiPathLine a ->
    "Expected a function, line or path type, inferred\n\n" ++
    "  " ++ pretty a

  ExpectedSg a ->
    "Expected a sigma type, inferred\n\n" ++
    "  " ++ pretty a

  ExpectedGlueTy a ->
    "Expected a glue type, inferred\n\n" ++
    "  " ++ pretty a

  ExpectedPathLine a ->
    "Expected a path type or a line type, inferred\n\n" ++
    "  " ++ pretty a

  ExpectedPathULineU a ->
    "Expected a path type or a line type in U, inferred\n\n" ++
    "  " ++ pretty a

  ExpectedNonDepFun a ->
    "Expected a non-dependent function type, inferred\n\n" ++
    "  " ++ pretty a

  CantInferLam ->
    "Can't infer type for lambda expression"

  CantInferPair ->
    "Can't infer type for pair expression"

  CantInferGlueTm ->
    "Can't infer type for glue expression"

  GlueTmSystemMismatch sys ->
    "Can't match glue system with expected Glue type system\n\n" ++
    "  " ++ pretty sys

  UnexpectedIType ->
    "The type of intervals I can be only used in function domains"

  NonNeutralCofInSystem ->
    "Only neutral cofibrations are allowed in systems"

displayErrInCxt :: String -> ErrInCxt -> IO ()
displayErrInCxt file (ErrInCxt e) = withPrettyArgs do

  let SourcePos path (unPos -> linum) (unPos -> colnum) = ?srcPos
      lnum = show linum
      lpad = map (const ' ') lnum

  putStrLn (show path ++ ":" ++ lnum ++ ":" ++ show colnum)
  putStrLn (lpad ++ " |")
  putStrLn (lnum ++ " | " ++ (lines file !! (linum - 1)))
  putStrLn (lpad ++ " | " ++ replicate (colnum - 1) ' ' ++ "^")
  putStrLn (showError e)
  putStrLn ""

----------------------------------------------------------------------------------------------------

setPos :: DontShow SourcePos -> (PosArg => a) -> a
setPos pos act = let ?srcPos = coerce pos in act; {-# inline setPos #-}

data Infer = Infer Tm ~VTy

check :: Elab (P.Tm -> VTy -> IO Tm)
check t topA = case t of

  P.Pos pos t ->
    setPos pos $ check t topA

  P.Let x ma t u -> do
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
    u <- define x va vt $ check u topA
    pure $! Let x a t u

  t -> case (t, unF (frc topA)) of

    (P.Lam x t, VPi a b) -> do
      Lam x <$!> bind x a (\v -> check t (capp b v))

    (P.Lam x t, VPath a l r) -> do
      t <- bindI x \i -> check t (a ∙ IVar i)
      convEndpoints (instantiate t (F I0)) l
      convEndpoints (instantiate t (F I1)) r
      pure $! PLam (quote l) (quote r) x t

    (P.Refl, VPath a l r) -> do
      constantICl a
      convEndpoints l r
      pure $! Refl (quote l)

    (P.Sym p, VPath a y x) -> do
      constantICl a
      p <- check p (VPath a x y)
      pure $! Sym (quote a) (quote x) (quote y) p

    (P.Trans p q, VPath a x z) -> do
      Infer p axy <- infer p
      (a', x', y) <- nonDepPath axy
      convICl a' a
      conv x' x
      q <- check q (VPath a y z)
      pure $! Trans (quote a) (quote x) (quote y) (quote z) p q

    (P.Lam x t, VLine a) -> do
      t <- bindI x \r -> check t (a ∙ IVar r)
      pure $ LLam x t

    (P.Pair t u, VSg a b) -> do
      t <- check t a
      u <- check u (b ∙ eval t)
      pure $! Pair t u

    (P.GlueTm base ts, VGlueTy a equivs) -> do
      base <- check base a
      ts   <- elabGlueTmSys base ts a (fst equivs)
      pure $ Glue base ts

    (t, topA) -> do
      Infer t a <- infer t
      convExInf a topA
      pure t

infer :: Elab (P.Tm -> IO Infer)
infer = \case
  P.Ident x -> case M.lookup x ?tbl of
    Nothing -> err $ NameNotInScope x
    Just e  -> case e of
      Top l a v  -> pure $! Infer (TopVar l (DontShow v)) a
      Local l a  -> pure $! Infer (LocalVar (lvlToIx ?dom l)) a
      LocalInt l -> err UnexpectedI

  P.LocalLvl x -> do
    unless (0 <= x && x < ?dom) (err LocalLvlNotInScope)
    let ix = lvlToIx ?dom x
    let Box a = ?localTypes !! fromIntegral ix
    pure $! Infer (LocalVar ix) a

  P.TopLvl x -> do
    unless (0 <= x && x < ?topLvl) (err TopLvlNotInScope)
    let (a, v) = ?topDefs !! fromIntegral (lvlToIx ?topLvl x)
    pure $! Infer (TopVar x (coerce v)) a

  P.ILvl{} -> err UnexpectedI
  P.I0 -> err UnexpectedI
  P.I1 -> err UnexpectedI
  P.I  -> err UnexpectedIType

  P.DepPath a t u -> do
    (x, a, _, src, tgt) <- elabBindMaybe a (F I0) (F I1)
    t <- check t src
    u <- check u tgt
    pure $! Infer (Path x a t u) VU

  P.Pos pos t ->
    setPos pos $ infer t

  P.Let x ma t u -> do
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
    Infer u b <- define x va vt $ infer u
    pure $! Infer (Let x a t u) b

  P.Pi x (P.unPos -> P.I) b -> do
    b <- bindI x \_ -> check b VU
    pure $ Infer (Line x b) VU

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
      VPath a l r -> do
        u <- checkI u
        pure $! Infer (PApp (quote l) (quote r) t u) (a ∙ evalInf u)
      VLine a -> do
        u <- checkI u
        pure $! Infer (LApp t u) (a ∙ evalInf u)
      a ->
        err $! ExpectedPiPathLine (quote a)

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
      a       -> err $! ExpectedSg (quote a)

  P.Proj2 t -> do
    Infer t a <- infer t
    case unF (frc a) of
      VSg a b -> pure $! Infer (Proj2 t) (b ∙ proj1 (evalf t))
      a       -> err $! ExpectedSg (quote a)

  P.U ->
    pure $ Infer U VU

  P.Path t u -> do
    Infer t a <- infer t
    u <- check u a
    pure $! Infer (Path "_" (Core.freshI \_ -> quote a) t u) VU

  P.Coe r r' a t -> do --
    r  <- checkI r
    r' <- checkI r'
    (x, a, va, src, tgt) <- elabBindMaybe a (evalI r) (evalI r')
    t <- check t src
    pure $! Infer (Coe r r' x a t) tgt

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
      VGlueTy a sys -> pure $! Infer (Unglue t (quote (fst sys))) a
      a             -> err $! ExpectedGlueTy (quote a)

  P.Com r r' a sys t -> do
    r  <- checkI r
    r' <- checkI r'
    (i, a, va, src, tgt) <- elabBindMaybe a (evalI r) (evalI r')
    t <- check t src
    -- NOTE: elabSysHCom happens to be correct for "com" as well. In the "hcom"
    -- case, the "a" type gets implicitly weakened under both a cof and an ivar
    -- binder when checking components. In the "com" case, "a" is already under
    -- an ivar binder, so it's only weakened under the cof. The boundary checks
    -- are exactly the same.
    sys <- elabSysHCom va r t sys
    pure $! Infer (Com r r' i a sys t) tgt

  P.Refl -> err CantInfer

  P.Sym p -> do
    Infer p axy <- infer p
    (a, x, y)   <- nonDepPath axy
    pure $! Infer (Sym (quote a) (quote x) (quote y) p) (VPath a y x)

  P.Trans p q -> do
    Infer p axy <- infer p
    (a, x, y)   <- nonDepPath axy
    Infer q ayz <- infer q
    (a', y', z) <- nonDepPath ayz
    convICl a' a
    conv y' y
    pure $! Infer (Trans (quote a) (quote x) (quote y) (quote z) p q) (VPath a x z)

  P.Ap f p -> do
    Infer f ab <- infer f
    (a, b) <- nonDepFun ab
    Infer p axy <- infer p
    (a', x, y) <- nonDepPath axy
    bindI "i" \(IVar -> i) -> conv (a' ∙ i) a
    let vf = evalf f
    pure $ Infer (Ap f (quote x) (quote y) p) (path (b ∙ x) (vf ∙ x) (vf ∙ y))


-- | Ensure that an IClosure is constant.
constantICl :: Elab (NamedIClosure -> IO ())
constantICl a = bindI "i" \(IVar -> i) -> bindI "j" \(IVar -> j) -> conv (a ∙ i) (a ∙ j)

-- | Ensure that a Closure is constant.
constantCl :: Elab (VTy -> NamedClosure -> IO ())
constantCl a cl = bind "x" a \x -> bind "y" a \y -> conv (cl ∙ x) (cl ∙ y)

-- | Ensure that a type is a non-dependent function.
nonDepFun :: Elab (Val -> IO (Val, NamedClosure))
nonDepFun a = case unF (frc a) of
  VPi a b -> constantCl a b >> pure (a, b)
  a       -> err $! ExpectedNonDepFun (quote a)

-- | Ensure that a type is a non-dependent path type.
nonDepPath :: Elab (Val -> IO (NamedIClosure, Val, Val))
nonDepPath a = case unF (frc a) of
  VPath a x y -> constantICl a >> pure (a, x, y)
  a           -> err $! ExpectedPath (quote a)

-- | Return binder name, type under binder, value of type under binder
--   , source type val, target type val
elabBindMaybe :: Elab (P.BindMaybe -> F I -> F I -> IO (Name, Tm, Val, Val, Val))
elabBindMaybe b r r' = case b of
  P.DontBind a -> do
    Infer a aty <- infer a
    case unF (frc aty) of
      VPath aty lhs rhs -> do
        isConstantU aty
        let va  = evalf a
            src = papp lhs rhs va r
            tgt = papp lhs rhs va r'
        let iname = pickIVarName
        bindI iname \i -> do
          a <- pure $ PApp (quote lhs) (quote rhs) (WkI iname a) (IVar i)
          pure (iname, a, eval a, src, tgt)
      VLine aty -> do
        isConstantU aty
        let va  = evalf a
            src = lapp va r
            tgt = lapp va r'
        let iname = pickIVarName
        bindI iname \i -> do
          a <- pure $ LApp (WkI iname a) (IVar i)
          pure (iname, a, eval a, src, tgt)
      a -> do
        err $! ExpectedPathLine (quote a)

  P.Bind x a -> do
    (a, va) <- bindI x \_ -> do {a <- check a VU; pure (a, eval a)}
    let src = instantiate a r
        tgt = instantiate a r'
    pure (x, a, va, src, tgt)

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

  P.ILvl x -> do
    unless (0 <= x && x < dom ?cof) (err LocalLvlNotInScope)
    pure $ IVar x

  P.LocalLvl (coerce -> x) -> do
    unless (0 <= x && x < dom ?cof) (err LocalLvlNotInScope)
    pure $ IVar x

  t -> do
    err ExpectedI

isConstantU :: Elab (NamedIClosure -> IO ())
isConstantU t = bindI "i" \i -> case unF (t ∘ IVar i) of
  VU -> pure ()
  a  -> err $ ExpectedPathULineU (quote a)

--------------------------------------------------------------------------------

checkCofEq :: Elab (P.CofEq -> IO CofEq)
checkCofEq (P.CofEq t u) = CofEq <$!> checkI t <*!> checkI u

checkCof :: Elab (P.Cof -> IO Cof)
checkCof = \case
  P.CTrue       -> pure CTrue
  P.CAnd eq cof -> CAnd <$!> checkCofEq eq <*!> checkCof cof

-- Systems
----------------------------------------------------------------------------------------------------

sysHComCompat :: Elab (Tm -> SysHCom -> IO ())
sysHComCompat t = \case
  SHEmpty              -> pure ()
  SHCons cof' x t' sys -> do
    case unF (evalCof cof') of
      VCFalse     -> pure ()
      VCTrue      -> bindI x \_ -> conv (eval t) (eval t')
      VCNe cof' _ -> bindCof cof' (bindI x \_ -> conv (eval t) (eval t'))
    sysHComCompat t sys

elabSysHCom :: Elab (VTy -> I -> Tm ->  P.SysHCom -> IO SysHCom)
elabSysHCom a r base = \case
  P.SHEmpty ->
    pure SHEmpty
  P.SHCons cof t sys -> do
    cof <- checkCof cof
    case unF (evalCof cof) of
      VCTrue  -> err NonNeutralCofInSystem
      VCFalse -> err NonNeutralCofInSystem
      VCNe ncof _ -> do
        sys <- elabSysHCom a r base sys
        bindCof ncof do

          -- desugar binders
          (x, t) <- case t of
            P.Bind x t -> do
              t <- bindI x \_ -> check t a -- "a" is weakened under vcof
              pure (x, t)
            P.DontBind t -> do
              Infer t tty <- infer t
              case unF (frc tty) of
                VPath pty lhs rhs -> do
                  let iname = pickIVarName
                  bindI iname \i -> do
                    conv (pty ∙ IVar i) a
                    t <- pure $ PApp (quote lhs) (quote rhs) (WkI iname t) (IVar i)
                    pure (iname, t)
                VLine pty -> do
                  let iname = pickIVarName
                  bindI iname \i -> do
                    conv (pty ∙ IVar i) a
                    t <- pure $ LApp (WkI iname t) (IVar i)
                    pure (iname, t)
                a -> do
                  err $! ExpectedPathLine (quote a)

          conv (instantiate t (frc r)) (eval base) -- check compatibility with base
          sysHComCompat t sys                      -- check compatibility with rest of system
          pure $ SHCons cof x t sys


sysCompat :: Elab (Tm -> Sys -> IO ())
sysCompat t = \case
  SEmpty            -> pure ()
  SCons cof' t' sys -> do
    case unF (evalCof cof') of
      VCTrue      -> conv (eval t) (eval t')
      VCFalse     -> pure ()
      VCNe cof' _ -> bindCof cof' $ conv (eval t) (eval t')
    sysCompat t sys

elabGlueTmSys :: Elab (Tm -> P.Sys -> VTy -> NeSys -> IO Sys)
elabGlueTmSys base ts a equivs = case (ts, equivs) of
  (P.SEmpty, NSEmpty) ->
    pure SEmpty
  (P.SCons cof t ts, NSCons (BindCofLazy cof' equiv) equivs) -> do
    cof <- checkCof cof
    case unF (evalCof cof) of
      VCTrue  -> err NonNeutralCofInSystem
      VCFalse -> err NonNeutralCofInSystem
      VCNe ncof _ -> do
        convNeCof (ncof^.extra) cof'
        ts <- elabGlueTmSys base ts a equivs
        bindCof ncof do
          let fequiv = frc equiv
          t <- check t (proj1 fequiv)
          conv (proj1f (proj2f fequiv) ∙ eval t) (eval base)
          sysCompat t ts
          pure $ SCons cof t ts
  (ts, equivs) ->
    err $! GlueTmSystemMismatch (quote equivs)

elabGlueTySys :: Elab (VTy -> P.Sys -> IO Sys)
elabGlueTySys a = \case
  P.SEmpty ->
    pure SEmpty
  P.SCons cof t sys -> do
    cof <- checkCof cof
    let vcof = evalCof cof
    case unF vcof of
      VCTrue  -> err NonNeutralCofInSystem
      VCFalse -> err NonNeutralCofInSystem
      VCNe ncof _ -> do
        sys <- elabGlueTySys a sys
        bindCof ncof do
          t <- check t (equivInto a)
          sysCompat t sys
          pure $ SCons cof t sys

----------------------------------------------------------------------------------------------------

type ElabTop a = (?printnf :: Maybe Name) => Elab a

defineTop :: Name -> VTy -> Val -> ElabTop a -> ElabTop a
defineTop x ~a ~v act =
  let ?topLvl  = ?topLvl + 1
      ?tbl     = M.insert x (Top ?topLvl a v) ?tbl
      ?topDefs = (a, v) : ?topDefs in
  let _ = ?topLvl; _ = ?tbl in
  act
{-# inline defineTop #-}

inferTop :: ElabTop (P.Top -> IO Top)
inferTop = \case

  P.TDef pos x ma t top -> setPos pos do

    case M.lookup x ?tbl of
      Just{} -> err TopShadowing
      _      -> pure ()

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

    -- withPrettyArgs $ putStrLn $ "\nNormal form of " ++ x ++ ":\n\n" ++ pretty0 (quote vt)

    case ?printnf of
      Just x' | x == x' -> withPrettyArgs do
        putStrLn $ "\nNormal form of " ++ x ++ ":\n\n" ++ pretty0 (quote vt)
        putStrLn ""
      _ -> pure ()

    top <- defineTop x va vt $ inferTop top
    pure $! TDef x a t top

  P.TEmpty ->
    pure TEmpty

elabTop :: Maybe Name -> FilePath -> String -> P.Top -> IO Top
elabTop printnf path file top = do
  let ?cof        = idSub 0
      ?dom        = 0
      ?env        = ENil
      ?tbl        = mempty
      ?srcPos     = initialPos path
      ?topLvl     = 0
      ?printnf    = printnf
      ?topDefs    = []
      ?localTypes = []
  catch (inferTop top) \(e :: ErrInCxt) -> do
    displayErrInCxt file e
    exitSuccess
