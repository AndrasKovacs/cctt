
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

convExInf :: Elab (Val -> Val -> IO ())
convExInf t u = if Conversion.conv t u
  then pure ()
  else err $ CantConvertExInf (quote t) (quote u)

convCof :: Elab (F VCof -> F VCof -> IO ())
convCof c c' = if Conversion.conv (unF c) (unF c')
  then pure ()
  else err $! CantConvertCof (quote (unF c)) (quote (unF c'))

convEndpoints :: Elab (Val -> Val -> IO ())
convEndpoints t u = if Conversion.conv t u
  then pure ()
  else err $ CantConvertEndpoints (quote t) (quote u)

--------------------------------------------------------------------------------

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
      ?dom = ?dom + 1
      ?tbl = M.insert x (Local ?dom a) ?tbl in
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
  | ExpectedPi Tm
  | ExpectedSg Tm
  | ExpectedGlueTy Tm
  | CantInferLam
  | CantInferPair
  | CantInferGlueTm
  | CantConvert Tm Tm
  | CantConvertCof Cof Cof
  | CantConvertEndpoints Tm Tm
  | CantConvertExInf Tm Tm
  | GlueTmSystemMismatch Sys
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
        CantConvertExInf t u ->
           "Can't convert expected type\n\n" ++
           "  " ++ pretty u ++ "\n\n" ++
           "and inferred type\n\n" ++
           "  " ++ pretty t
        CantConvert t u ->
           "Can't convert\n\n" ++
           "  " ++ pretty u ++ "\n\n" ++
           "and\n\n" ++
           "  " ++ pretty t
        CantConvertEndpoints t u ->
           "Can't convert expected path endpoint\n\n" ++
           "  " ++ pretty u ++ "\n\n" ++
           "to\n\n" ++
           "  " ++ pretty t
        CantConvertCof c1 c2 ->
           "Can't convert expected path endpoint\n\n" ++
           "  " ++ pretty c1 ++ "\n\n" ++
           "to\n\n" ++
           "  " ++ pretty c2
        NameNotInScope x ->
           "Name not in scope: " ++ x
        TopShadowing ->
           "Duplicate top-level name"
        UnexpectedI ->
           "Unexpected interval expression"
        ExpectedI ->
           "Expected an interval expression"
        ExpectedPi a ->
           "Expected a function type, inferred" ++
           "  " ++ pretty a
        ExpectedSg a ->
           "Expected a sigma type, inferred" ++
           "  " ++ pretty a
        ExpectedGlueTy a ->
           "Expected a glue type, inferred" ++
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

    (P.Lam x t, VPathP a l r) -> do
      t <- bindI x \r -> check t (icapp a (IVar r))
      convEndpoints (instantiate t (F I0)) l
      convEndpoints (instantiate t (F I1)) r
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

  P.I0 -> err UnexpectedI
  P.I1 -> err UnexpectedI

  P.PathP x a t u -> do
    a <- bindI x \_ -> check a VU
    t <- check t (instantiate a (F I0))
    u <- check u (instantiate a (F I1))
    pure $! Infer (PathP x a t u) VU

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
      a ->
        err $! ExpectedPi (quote a)

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

  P.Path Nothing t u -> do
    Infer t a <- infer t
    u <- check u a
    pure $! Infer (PathP "_" (Core.freshI \_ -> quote a) t u) VU

  P.Path (Just a) t u -> do
    a <- bindI "_" \_ -> check a VU
    let va = instantiate a (F I0) -- instantiation doesn't matter
    t <- check t va
    u <- check u va
    pure $! Infer (PathP "_" a t u) VU

  P.Coe r r' x a t -> do --
    r  <- checkI r
    r' <- checkI r'
    a  <- bindI x \_ -> check a VU
    t  <- check t (instantiate a (evalI r))
    pure $! Infer (Coe r r' x a t) (instantiate a (evalI r'))

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
      a               -> err $! ExpectedGlueTy (quote a)

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

  P.Com r r' i a sys t -> do
    r       <- checkI r
    r'      <- checkI r'
    (a, va) <- bindI i \_ -> do {a <- check a VU; pure (a, eval a)}
    t       <- check t (instantiate a (evalI r))

    -- NOTE: elabSysHCom happens to be correct for "com" as well. In the "hcom"
    -- case, the "a" type gets implicitly weakened under both a cof and an ivar
    -- binder when checking components. In the "com" case, "a" is already under
    -- an ivar binder, so it's only weakened under the cof. The boundary checks
    -- are exactly the same.
    sys     <- elabSysHCom va r t sys
    pure $! Infer (Com r r' i a sys t) (instantiate a (evalI r'))

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

-- Systems
----------------------------------------------------------------------------------------------------

sysHComCompat :: Elab (Tm -> SysHCom -> IO ())
sysHComCompat t = \case
  SHEmpty              -> pure ()
  SHCons cof' x t' sys -> do
    case unF (evalCof cof') of
      VCFalse     -> pure ()
      (F -> cof') -> bindVCof cof' (bindI x \_ -> conv (eval t) (eval t'))
    sysHComCompat t sys

elabSysHCom :: Elab (VTy -> I -> Tm ->  P.SysHCom -> IO SysHCom)
elabSysHCom a r base = \case
  P.SHEmpty ->
    pure SHEmpty
  P.SHCons cof x t sys -> do
    cof <- checkCof cof
    let vcof = evalCof cof
    case unF vcof of
      VCFalse -> do
        elabSysHCom a r base sys
      (F -> vcof) -> do
        sys <- elabSysHCom a r base sys
        bindVCof vcof do
          t <- bindI x \_ -> check t a             -- "a" is weakened under vcof
          conv (instantiate t (frc r)) (eval base) -- check compatibility with base
          sysHComCompat t sys                      -- check compatibility with rest of system
          pure $ SHCons cof x t sys

sysCompat :: Elab (Tm -> Sys -> IO ())
sysCompat t = \case
  SEmpty            -> pure ()
  SCons cof' t' sys -> do
    case unF (evalCof cof') of
      VCFalse     -> pure ()
      (F -> cof') -> bindVCof cof' $ conv (eval t) (eval t')
    sysCompat t sys

elabGlueTmSys :: Elab (Tm -> P.Sys -> VTy -> NeSys -> IO Sys)
elabGlueTmSys base ts a equivs = case (ts, equivs) of
  (P.SEmpty, NSEmpty) ->
    pure SEmpty
  (P.SCons cof t ts, NSCons (BindCofLazy cof' equiv) equivs) -> do
    cof <- checkCof cof
    let vcof = evalCof cof
    convCof vcof (frc cof')
    ts <- elabGlueTmSys base ts a equivs
    bindVCof vcof do
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
      VCFalse ->
        elabGlueTySys a sys
      (F -> vcof) -> do
        sys <- elabGlueTySys a sys
        bindVCof vcof do
          t <- check t (equivInto a)
          sysCompat t sys
          pure $ SCons cof t sys

----------------------------------------------------------------------------------------------------

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
    debug ["TOPNF", x, pretty (quote vt)]
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
