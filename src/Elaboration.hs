{-# options_ghc -Wno-unused-top-binds #-}

module Elaboration (elaborate) where

import Control.Exception
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import System.FilePath
import System.Exit

import Common hiding (debug)
import Core hiding (bindI, bindCof, define, eval, evalCof, evalI, evalSys)
import CoreTypes
import Interval
import Quotation
import ElabState
import Errors
import Parser

import qualified Common
import qualified Conversion
import qualified Core
import qualified Presyntax as P
import qualified LvlMap as LM

import Pretty


-- Wrapped functions
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

convReflEndpoints :: Elab (Val -> Val -> IO ())
convReflEndpoints t u = if Conversion.conv t u
  then pure ()
  else err $ CantConvertReflEndpoints (quote t) (quote u)

eval :: NCofArg => DomArg => EnvArg => Tm -> Val
eval t = let ?sub = idSub (dom ?cof); ?recurse = DontRecurse in Core.eval t

evalIn :: NCofArg => DomArg => Env -> Tm -> Val
evalIn env t = let ?env = env in eval t

evalSys :: NCofArg => DomArg => EnvArg => Sys -> VSys
evalSys sys = let ?sub = idSub (dom ?cof); ?recurse = DontRecurse in Core.evalSys sys

instantiate :: NCofArg => DomArg => EnvArg => Tm -> I -> Val
instantiate t i = let ?sub = idSub (dom ?cof) `ext` i; ?recurse = DontRecurse
                  in Core.eval t

evalCof :: NCofArg => Cof -> VCof
evalCof cof = let ?sub = idSub (dom ?cof) in Core.evalCof cof

evalI :: NCofArg => I -> I
evalI i = let ?sub = idSub (dom ?cof) in Core.evalI i

debug :: PrettyArgs [String] -> Elab (IO ())
debug x = withPrettyArgs (Common.debug x)

setPos :: DontShow SourcePos -> (PosArg => a) -> a
setPos pos act = let ?srcPos = coerce pos in act; {-# inline setPos #-}

frcPos :: P.Tm -> (PosArg => P.Tm -> a) -> PosArg => a
frcPos t act = case t of
  P.Pos p t -> setPos p (act t)
  t         -> act t
{-# inline frcPos #-}

-- | Create fibrant closure from term in extended context.
makeNCl :: Elab (Name -> Tm -> NamedClosure)
makeNCl x t = NCl x $ CEval $ EC (idSub (dom ?cof)) ?env DontRecurse t
{-# inline makeNCl #-}

----------------------------------------------------------------------------------------------------

data Infer = Infer Tm ~VTy deriving Show

data Split
  = DConHead DConInfo [P.Tm]
  | TyConHead TyConInfo [P.Tm]
  | SplitInfer {-# unpack #-} Infer
  deriving Show

check :: Elab (P.Tm -> VTy -> IO Tm)
check t topA = frcPos t \case

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
    u <- define x va a vt $ check u topA
    pure $! Let x a t u

  t -> case (t, frc topA) of

    (P.Lam x ann t, VPi a b) -> do
      ~qa <- case ann of Nothing -> pure (quote a)
                         Just a' -> do a' <- check a' VU
                                       conv (eval a') a
                                       pure a'
      Lam x <$!> bind x a qa (\v -> check t (b ∙ v))

    (P.Split cs, VPi a b) -> do
      (tyinfo, params) <- case frc a of
        VTyCon inf ps -> pure (inf, ps)
        a             -> err $ ExpectedInductiveType (quote a)
      frz <- readIORef (tyinfo^.frozen)
      unless frz $ err $ GenericError "Can't case split on the type that's being defined"
      cons <- readIORef (tyinfo^.constructors)
      cs <- elabCases params b (LM.elems cons) cs
      pure $! Split (b^.name) (quote b) cs

    (P.Lam x ann t, VPath a l r) -> do
      case ann of Nothing               -> pure ()
                  Just (P.unPos -> P.I) -> pure ()
                  Just _                -> err $ GenericError "Expected an interval binder"
      t <- bindI x \i -> check t (a ∙ IVar i)
      convEndpoints (instantiate t I0) l
      convEndpoints (instantiate t I1) r
      pure $! PLam (quote l) (quote r) x t

    (P.PLam l r x t, VPath a l' r') -> do
      t <- bindI x \i -> check t (a ∙ IVar i)
      convEndpoints (instantiate t I0) l'
      convEndpoints (instantiate t I1) r'
      l <- check l (a ∙ I0)
      r <- check r (a ∙ I1)
      convEndpoints (eval l) l'
      convEndpoints (eval r) r'
      pure $! PLam l r x t

    (P.Refl, VPath a l r) -> do
      constantICl a
      convReflEndpoints l r
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

    (P.Lam x ma t, VLine a) -> do
      case ma of Nothing               -> pure ()
                 Just (P.unPos -> P.I) -> pure ()
                 Just _                -> err $ GenericError "Expected an interval binder"
      t <- bindI x \r -> check t (a ∙ IVar r)
      pure $ LLam x t

    (P.Pair t u, VSg a b) -> do
      t <- check t a
      u <- check u (b ∙ eval t)
      pure $! Pair (b^.name) t u

    (P.GlueTm base eqs ts, VGlueTy a equivs) -> do
      ~eqs <- case eqs of
        Nothing -> pure (quote (fst equivs))
        Just eqs -> do
          eqs <- elabGlueTySys a eqs
          pure eqs
      base <- check base a
      ts   <- elabGlueTmSys base ts a (fst equivs)
      pure $ Glue base eqs ts

    -- inferring non-dependent motive for case
    (P.Case t Nothing cs, b) -> do
      Infer t a <- infer t
      (typeinfo, params) <- case frc a of
        VTyCon inf ps -> pure (inf, ps)
        a             -> err $ ExpectedInductiveType (quote a)
      let qb = bind "_" a (quote a) \_ -> quote b
      let bv = NCl "_" $ CConst b
      frz <- readIORef $ typeinfo^.frozen
      unless frz $ err $ GenericError "Can't case split on the type that's being defined"
      cons <- readIORef $ typeinfo^.constructors
      cs <- elabCases params bv (LM.elems cons) cs
      pure $ Case t "_" qb cs

    (P.Hole i p, a) -> setPos p $ withPrettyArgs do
      putStrLn ("HOLE ?" ++ maybe (sourcePosPretty ?srcPos) id i)
      putStrLn ("  : " ++ pretty (quote a) ++ "\n")
      pure (Hole i p)

    (t, VWrap x a) -> do
      t <- check t a
      pure $! Pack x t

    (t, VTyCon tyinf ps) -> do
      split t >>= \case
        DConHead dci sp -> do
          unless (dci^.tyConInfo.tyId == tyinf^.tyId) $ withPrettyArgs $
            err $ GenericError $
              "No such constructor for expected type:\n\n  "
              ++ pretty (quote (VTyCon tyinf ps))
          sp <- checkSp ps sp (dci^.fieldTypes)
          pure $ DCon dci sp

        TyConHead{} ->
          err $ GenericError $ withPrettyArgs $
            "Expected inductive type:\n\n  " ++ pretty (quote (VTyCon tyinf ps)) ++
            "\n\nbut the expression is a type constructor"

        SplitInfer (Infer t a) -> do
          convExInf a topA
          pure t

    (t, topA) -> do
      Infer t a <- infer t
      convExInf a topA
      pure t

splitIdent :: Elab (Name -> Ix -> Locals -> [P.Tm] -> IO Split)
splitIdent x ix ls sp = case ls of

  LNil -> do
    st <- getState
    case M.lookup x (st^.top) of
      Nothing                 -> err $ NameNotInScope x
      Just (TEDef inf)        -> SplitInfer <$!> inferSp (TopVar inf) (inf^.defTyVal) sp
      Just (TETyCon inf)      -> pure $ TyConHead inf sp
      Just (TERec Nothing)    -> err $ GenericError $
                                       "Can't infer type for recursive call. "++
                                       "Put a type annotation on the top-level definition."
      Just (TERec (Just inf)) -> SplitInfer <$!> inferSp (RecursiveCall inf) (inf^.recTyVal) sp
      Just (TEDCon inf)       -> pure $ DConHead inf sp

  LBind ls x' a qa | x == x' -> SplitInfer <$!> inferSp (LocalVar ix) a sp
                   | True    -> splitIdent x (ix + 1) ls sp
  LBindI ls x'     | x == x' -> err UnexpectedI
                   | True    -> splitIdent x ix ls sp
  LCof ls _                  -> splitIdent x ix ls sp

goSplit :: Elab (P.Tm -> [P.Tm] -> P.Tm -> IO Split)
goSplit t sp topT = frcPos t \case

  P.Ident x -> do
    splitIdent x 0 ?locals sp

  P.App t u -> do
    goSplit t (u:sp) topT

  P.TopLvl x Nothing -> do
    st <- getState
    case LM.lookup x (st^.top') of
      Nothing ->
        err $ GenericError $ "No top-level definition with de Bruijn level"
      Just (TEDef' inf) ->
        SplitInfer <$!> inferSp (TopVar inf) (inf^.defTyVal) sp
      Just (TETyCon' inf) ->
        pure $ TyConHead inf sp

  P.TopLvl x (Just y) -> do
    st <- getState
    case LM.lookup x (st^.top') of
      Nothing ->
        err $ GenericError $ "No type constructor with de Bruijn level"
      Just (TEDef' _) ->
        err $ GenericError $ "No type constructor with de Bruijn level"
      Just (TETyCon' inf) -> do
        cons <- readIORef (inf^.constructors)
        case LM.lookup y cons of
          Nothing ->
            err $ GenericError $ "No data constructor with de Bruijn level"
          Just dinf ->
            pure $ DConHead dinf sp

  t -> do
    Infer t a <- inferNonSplit t
    SplitInfer <$!> inferSp t a sp

split :: Elab (P.Tm -> IO Split)
split t = goSplit t [] t

inferSp :: Elab (Tm -> VTy -> [P.Tm] -> IO Infer)
inferSp t a sp = case sp of
  []   -> pure $ Infer t a
  u:sp -> case frc a of
    VPi a b -> do
      u <- check u a
      inferSp (App t u) (b ∙ eval u) sp
    VPath a l r -> do
      u <- checkI u
      inferSp (PApp (quote l) (quote r) t u) (a ∙ evalI u) sp
    VLine a -> do
      u <- checkI u
      inferSp (LApp t u) (a ∙ evalI u) sp
    a ->
      err $! ExpectedPiPathLine (quote a)

checkSp :: Elab (Env -> [P.Tm] -> Tel -> IO Spine)
checkSp env sp fs = case (sp, fs) of
  (t:sp, TCons x a fs) -> do
    t  <- check t (evalIn env a)
    sp <- checkSp (EDef env (eval t)) sp fs
    pure $ SPCons t sp
  ([], TNil) ->
    pure $ SPNil
  (_:_, TNil) ->
    err $ GenericError "Constructor applied to too few arguments"
  ([], TCons{}) ->
    err $ GenericError "Constructor applied to too many arguments"

infer :: Elab (P.Tm -> IO Infer)
infer t = split t >>= \case

  -- no params + saturated
  DConHead inf sp -> case inf^.tyConInfo.paramTypes of
    TNil -> do
      sp <- checkSp ENil sp (inf^.fieldTypes)
      pure $ Infer (DCon inf sp) (VTyCon (inf^.tyConInfo) ENil)
    _  ->
      err $ GenericError $ "Can't infer type for a data constructor which has type parameters"

  -- saturated
  TyConHead inf sp -> do
    sp <- checkSp ENil sp (inf^.paramTypes)
    pure $ Infer (TyCon inf sp) VU

  SplitInfer inf -> do
    pure inf

inferNonSplit :: Elab (P.Tm -> IO Infer)
inferNonSplit t = frcPos t \case
  P.Pos{}    -> impossible
  P.Ident{}  -> impossible
  P.TopLvl{} -> impossible
  P.App{}    -> impossible

  P.LocalLvl x -> do
    unless (0 <= x && x < ?dom) (err LocalLvlNotInScope)
    let ix = lvlToIx ?dom x
    let Box a = lookupLocalType ix ?locals
    pure $! Infer (LocalVar ix) a

  P.ILvl{} -> err UnexpectedI
  P.I0     -> err UnexpectedI
  P.I1     -> err UnexpectedI
  P.I      -> err UnexpectedIType

  P.DepPath a t u -> do
    (x, a, _, src, tgt) <- elabBindMaybe a I0 I1
    t <- check t src
    u <- check u tgt
    pure $! Infer (Path x a t u) VU

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
    Infer u b <- define x va a vt $ infer u
    pure $! Infer (Let x a t u) b

  P.Pi x (P.unPos -> P.I) b -> do
    b <- bindI x \_ -> check b VU
    pure $ Infer (Line x b) VU

  P.Pi x a b -> do
    a <- check a VU
    b <- bind x (eval a) a \_ -> check b VU
    pure $ Infer (Pi x a b) VU

  P.PApp l r t u -> do
    Infer t a <- infer t
    case frc a of
      VPath a l' r' -> do
        u <- checkI u
        l <- check l (a ∙ I0)
        r <- check r (a ∙ I1)
        convEndpoints l' (eval l)
        convEndpoints r' (eval r)
        pure $! Infer (PApp l r t u) (a ∙ evalI u)
      a ->
        err $! ExpectedPath (quote a)

  P.Lam x Nothing t ->
    err CantInferLam

  P.Lam x (Just a) t -> case P.unPos a of
    -- line type
    P.I -> bindI x \i -> do
      Infer t a <- infer t
      pure $! Infer (LLam x t) (VLine $ NICl x $ ICBindI (BindI x i a))

    a -> do
      a <- eval <$!> check a VU
      (t, b, qb) <- bind x a (quote a) \_ -> do
        Infer t b <- infer t
        let qb = quote b
        pure (t, b, qb)
      pure $! Infer (Lam x t) (VPi a (makeNCl x qb))

  -- we infer non-dependent path types to explicit path lambdas.
  P.PLam l r x t -> do
    Infer l a <- infer l
    r <- check r a
    t <- bindI x \i -> check t a
    let vl = eval l
        vr = eval r
    convEndpoints vl (instantiate t I0)
    convEndpoints vr (instantiate t I1)
    pure $! Infer (PLam l r x t) (VPath (NICl x (ICConst a)) vl vr)

  P.Sg x a b -> do
    a <- check a VU
    b <- bind x (eval a) a \_ -> check b VU
    pure $ Infer (Sg x a b) VU

  P.Pair{} ->
    err CantInferPair

  P.Proj1 t -> do
    Infer t a <- infer t
    case frc a of
      VSg a b -> pure $ Infer (Proj1 t (b^.name)) a
      a       -> err $! ExpectedSg (quote a)

  P.Proj2 t -> do
    Infer t a <- infer t
    case frc a of
      VSg a b -> pure $! Infer (Proj2 t (b^.name)) (b ∙ proj1 (b^.name) (eval t))
      a       -> err $! ExpectedSg (quote a)

  P.Wrap x a -> do
    a <- check a VU
    pure $! Infer (Wrap x a) VU

  P.ProjField t x -> do
    Infer t a <- infer t
    elabProjField x t (eval t) a

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

  P.GlueTm base (Just eqs) sys -> do
    Infer base a <- infer base
    eqs <- elabGlueTySys a eqs
    case evalSys eqs of
      VSTotal _ -> impossible
      VSNe veqs -> do
        sys <- elabGlueTmSys base sys a (fst veqs)
        pure $! Infer (Glue base eqs sys) (VGlueTy a veqs)

  P.GlueTm _ Nothing _ -> do
    err CantInferGlueTm

  P.Unglue t -> do
    Infer t a <- infer t
    case frc a of
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
    let vf = eval f
    pure $ Infer (Ap f (quote x) (quote y) p) (path (b ∙ x) (vf ∙ x) (vf ∙ y))

  P.Hole i p -> setPos p do
    err CantInferHole

  P.Case t (Just (x, b)) cs -> do
    Infer t a <- infer t
    (tyinfo, params) <- case frc a of
      VTyCon i ps -> pure (i, ps)
      a           -> err $ ExpectedInductiveType (quote a)
    b <- bind x a (quote a) \_ -> check b VU
    let bv = makeNCl x b
    frz <- readIORef (tyinfo^.frozen)
    unless frz $ err $ GenericError "Can't case split on the type that's being defined"
    cons <- readIORef (tyinfo^.constructors)
    cs <- elabCases params bv (LM.elems cons) cs
    pure $! Infer (Case t x b cs) (bv ∙ eval t)

  P.Case _ Nothing _ ->
    err $ GenericError "Can't infer type for case expression"

  P.Split _ ->
    err $ GenericError "Can't infer type for case splitting function"

----------------------------------------------------------------------------------------------------

elabCase :: Elab (Lvl -> Env -> Tel -> Val -> [Name] -> P.Tm -> IO Tm)
elabCase conid tyenv fieldtypes rhstype xs body = case (fieldtypes, xs) of
  (TNil, []) ->
    check body rhstype
  (TCons _ a fieldtypes, x:xs) -> do
    let ~va = evalIn tyenv a
    bind x va (quote va) \x ->
      elabCase conid (EDef tyenv x) fieldtypes rhstype xs body
  _ -> do
    err $ GenericError "Wrong number of constructor fields"

caseLhsSp :: Lvl -> [Name] -> VDSpine
caseLhsSp dom []     = VDNil
caseLhsSp dom (_:xs) = VDCons (VNe (NLocalVar dom) mempty) (caseLhsSp (dom + 1) xs)

elabCases :: Elab (
     Env -> NamedClosure -> [DConInfo] -> [(Name, [Name], P.Tm)] -> IO Cases)
elabCases params b contypes cs = case (contypes, cs) of
  ([], []) ->
    pure CSNil
  (dci:cons, (x', xs, body):cs) | dci^.name == x' -> do
    let rhstype = b ∙ VDCon dci (caseLhsSp ?dom xs)
    t  <- elabCase (dci^.conId) params (dci^.fieldTypes) rhstype xs body
    cs <- elabCases params b contypes cs
    pure $ CSCons (dci^.name) xs t cs
  _ -> do
    err CaseMismatch

----------------------------------------------------------------------------------------------------

elabProjField :: Elab (Name -> Tm -> Val -> VTy -> IO Infer)
elabProjField x t ~tv a = case frc a of
  VSg a b    -> if x == b^.name then
                  pure (Infer (Proj1 t x) a)
                else
                  elabProjField x (Proj2 t (b^.name))
                                  (proj2 (b^.name) tv)
                                  (b ∙ proj1 (b^.name) tv)
  VWrap x' a -> if x == x' then
                  pure (Infer (Unpack t x) a)
                else
                  err $ NoSuchField (quote (VWrap x' a))
  a          -> err $ NoSuchField (quote a)

-- | Ensure that an IClosure is constant.
constantICl :: Elab (NamedIClosure -> IO ())
constantICl a = bindI "i" \(IVar -> i) -> bindI "j" \(IVar -> j) -> conv (a ∙ i) (a ∙ j)

-- | Ensure that a Closure is constant.
constantCl :: Elab (VTy -> NamedClosure -> IO ())
constantCl a cl = bind "x" a (quote a) \x -> bind "y" a (quote a) \y -> conv (cl ∙ x) (cl ∙ y)

-- | Ensure that a type is a non-dependent function.
nonDepFun :: Elab (Val -> IO (Val, NamedClosure))
nonDepFun a = case frc a of
  VPi a b -> constantCl a b >> pure (a, b)
  a       -> err $! ExpectedNonDepFun (quote a)

-- | Ensure that a type is a non-dependent path type.
nonDepPath :: Elab (Val -> IO (NamedIClosure, Val, Val))
nonDepPath a = case frc a of
  VPath a x y -> constantICl a >> pure (a, x, y)
  a           -> err $! ExpectedPath (quote a)

-- | Return binder name, type under binder, value of type under binder
--   , source type val, target type val
elabBindMaybe :: Elab (P.BindMaybe -> I -> I -> IO (Name, Tm, Val, Val, Val))
elabBindMaybe b r r' = case b of
  P.DontBind a -> do
    Infer a aty <- infer a
    case frc aty of
      VPath aty lhs rhs -> do
        isConstantU aty
        let va  = eval a
            src = papp lhs rhs va r
            tgt = papp lhs rhs va r'
        let iname = pickIVarName
        bindI iname \i -> do
          a <- pure $ PApp (quote lhs) (quote rhs) (WkI iname a) (IVar i)
          pure (iname, a, eval a, src, tgt)
      VLine aty -> do
        isConstantU aty
        let va  = eval a
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

identI :: Elab (Name -> IVar -> Locals -> IO I)
identI x idom = \case
  LNil                      -> err $ GenericError $ "Interval variable not in scope"
  LBind ls x' _ _ | x == x' -> err ExpectedI
                  | True    -> identI x idom ls
  LBindI ls x'    | x == x' -> pure $ IVar (idom - 1)
                  | True    -> identI x (idom - 1) ls
  LCof ls _                 -> identI x idom ls

checkI :: Elab (P.Tm -> IO I)
checkI t = frcPos t \case
  P.Pos{} -> impossible
  P.I0    -> pure I0
  P.I1    -> pure I1

  P.Ident x -> do
    identI x (dom ?cof) ?locals

  P.ILvl x -> do
    unless (0 <= x && x < dom ?cof)
           (err $ GenericError "Interval level not in scope")
    pure $ IVar x

  P.LocalLvl (coerce -> x) -> do
    unless (0 <= x && x < dom ?cof)
           (err $ GenericError "Interval level not in scope")
    pure $ IVar x

  t -> do
    err ExpectedI

isConstantU :: Elab (NamedIClosure -> IO ())
isConstantU t = bindI "i" \i -> case frc (t ∙ IVar i) of
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
    case evalCof cof' of
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
    case evalCof cof of
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
              case frc tty of
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
    case evalCof cof' of
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
    case evalCof cof of
      VCTrue  -> err NonNeutralCofInSystem
      VCFalse -> err NonNeutralCofInSystem
      VCNe ncof _ -> do
        convNeCof (ncof^.extra) cof'
        ts <- elabGlueTmSys base ts a equivs
        bindCof ncof do
          let fequiv = frc equiv
          t <- check t (proj1 "Ty" fequiv)
          conv (proj1 "f" (proj2 "Ty" fequiv) ∙ eval t) (eval base)
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
    case vcof of
      VCTrue  -> err NonNeutralCofInSystem
      VCFalse -> err NonNeutralCofInSystem
      VCNe ncof _ -> do
        sys <- elabGlueTySys a sys
        bindCof ncof do
          t <- check t (equivInto a)
          sysCompat t sys
          pure $ SCons cof t sys

----------------------------------------------------------------------------------------------------

guardTopShadowing :: Elab (Name -> IO ())
guardTopShadowing x = do
  st <- getState
  case M.lookup x (st^.top) of
    Nothing -> pure ()
    Just (TEDef inf  ) -> err $ TopShadowing (inf^.pos)
    Just (TETyCon inf) -> err $ TopShadowing (inf^.pos)
    Just (TEDCon inf ) -> err $ TopShadowing (inf^.pos)
    Just (TERec _    ) -> impossible

elabTop :: P.Top -> IO Top
elabTop = \case

  P.TDef pos x ma t top -> withTopElab $ setPos pos do
    guardTopShadowing x

    ma <- case ma of
      Nothing -> pure Nothing
      Just a  -> do {a <- check a VU; pure (Just (a, eval a))}

    _

    -- declareTopDef x (snd <$!> ma) (coerce pos) \l -> do

    --   (t, a, va) <- case ma of
    --     Nothing      -> do {Infer t a <- infer t; pure (t, quote a, a)}
    --     Just (a, va) -> do {t <- check t va; pure (t, a, va)}

    --   -- recursive evaluation
    --   let ~tv = (let ?sub = idSub (dom ?cof); ?recurse = Recurse (coerce tv) in Core.eval t)

    --   finalizeTopDef l x va tv (coerce pos)

    --   printnf <- getTop <&> (^.printingOpts.printNf)
    --   case printnf of
    --     Just x' | x == x' -> withPrettyArgs do
    --       putStrLn $ "\nNormal form of " ++ x ++ ":\n\n" ++ pretty0 (quote tv)
    --       putStrLn ""
    --     _ -> pure ()

    --   top <- elabTop top
    --   pure $ TDef x a t top

  P.TImport pos modname top -> withTopElab $ setPos pos do
    st <- getState
    let dirpath = takeDirectory (st^.loadState.currentPath)
        newpath = dirpath </> (modname <.> "cctt")
    if S.member newpath (st^.loadState.loadedFiles) then do
      elabTop top
    else if elem newpath (st^.loadCycle) then do
      err $ ImportCycle (st^.currentPath) (st^.loadState.loadCycle)
    else do
      importTop <- elabPath (Just pos) newpath
      top <- elabTop top
      pure $! importTop <> top

  P.TData pos tyname ps cs top -> withTopElab $ setPos pos do
    guardTopShadowing tyname
    ps   <- elabTelescope ps
    _
    -- (tyid, cs) <- declareNewTyCon tyname ps (coerce pos) \tyid -> do
    --   cs <- bindTelescope ps do
    --     elabConstructors tyid 0 cs
    --   pure (tyid, cs)
    -- finalizeTyCon tyid
    -- tbl  <- getTop <&> (^.tbl)
    -- top  <- elabTop top
    -- pure $ TData tyname ps cs top

  P.TEmpty ->
    pure TEmpty

----------------------------------------------------------------------------------------------------

elabConstructors :: Elab (Lvl -> Lvl -> [(DontShow SourcePos, Name, [(Name, P.Ty)])]
                          -> IO [(Name, Tel)])
elabConstructors tyid conid = \case
  [] ->
    pure []
  (pos, x, fs):cs -> setPos pos do
    guardTopShadowing x
    _
    -- fs <- elabTelescope fs
    -- cs <- addDCon x tyid conid fs (coerce pos) do
    --   elabConstructors tyid (conid + 1) cs
    -- pure ((x, fs):cs)

elabTelescope :: Elab ([(Name, P.Ty)] -> IO Tel)
elabTelescope = \case
  [] -> pure TNil
  (x, a):ps -> do
    a <- check a VU
    bind x (eval a) a \_ -> do
      ps <- elabTelescope ps
      pure $ TCons x a ps

bindTelescope :: Tel -> Elab a -> Elab a
bindTelescope ps act = case ps of
  TNil         -> act
  TCons x a ps -> bind x (eval a) a \_ -> bindTelescope ps act
{-# inline bindTelescope #-}

----------------------------------------------------------------------------------------------------

elabPath :: Maybe (DontShow SourcePos) -> FilePath -> IO Top
elabPath pos path = do
  oldpath  <- getState <&> (^.currentPath)
  oldCycle <- getState <&> (^.loadCycle)
  oldSrc   <- getState <&> (^.currentSrc)

  file <- readFile path `catch` \(e :: IOError) -> do
    case pos of
      Nothing -> do
        putStrLn $ "Can't open file: " ++ path
        exitSuccess
      Just pos -> withTopElab $ setPos pos do
        err $ CantOpenFile path

  (!top, !tparse) <- timed (parseString path file)
  modState $ (currentPath .~ path)
           . (loadCycle   .~ (path : oldCycle))
           . (parsingTime +~ tparse)
           . (currentSrc  .~ file)
  top <- elabTop top
  modState $ (currentPath .~ oldpath)
           . (loadCycle   .~ oldCycle)
           . (currentSrc  .~ oldSrc)
           . (loadedFiles %~ S.insert path)
  pure top

elaborate :: FilePath -> IO Top
elaborate path = elabPath Nothing path `catch` \(e :: ErrInCxt) -> do
  displayErrInCxt e
  exitSuccess
