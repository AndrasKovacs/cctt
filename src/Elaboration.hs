{-# options_ghc -Wno-unused-top-binds #-}

module Elaboration (elaborate) where

import Control.Exception
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import System.FilePath
import System.Exit

import Common hiding (debug)
import Core hiding (bindI, bindCof, define, eval, evalCof, evalI, evalSys, evalBoundary)
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

import Pretty hiding (bind, bindI)
import qualified Pretty

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

-- TODO OPT: unbox
data Split
  = DConHead DConInfo [P.Tm]
  | TyConHead TyConInfo [P.Tm]
  | HTyConHead HTyConInfo [P.Tm]
  | HDConHead HDConInfo [P.Tm]
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
      ~qa <- case ann of
        P.LANone         -> pure (quote a)
        P.LAAnn a'       -> do a' <- check a' VU
                               conv (eval a') a
                               pure a'
        P.LADesugared a' -> check a' VU
      Lam x <$!> bind x a qa (\v -> check t (b ∙ v))

    (P.Split cs, VPi a b) -> case frc a of
      VTyCon tyinfo params -> do
        frz <- readIORef (tyinfo^.frozen)
        unless frz $ err $ GenericError "Can't case split on the type that's being defined"
        cons <- readIORef (tyinfo^.constructors)
        cs <- elabCases params b (LM.elems cons) cs
        pure $! Split (b^.name) (quote b) cs
      VHTyCon inf params -> do
        frz <- readIORef (inf^.frozen)
        unless frz $ err $ GenericError "Can't case split on the type that's being defined"
        cons <- readIORef (inf^.constructors)
        cs <- elabHCases params b (LM.elems cons) cs CSNil
        pure $! HSplit (b^.name) (quote b) cs
      _ ->
        err $ ExpectedInductiveType (quote a)

    (P.Lam x ann t, VPath a l r) -> do
      case ann of P.LANone                 -> pure ()
                  P.LAAnn (P.unPos -> P.I) -> pure ()
                  P.LADesugared{}          -> pure ()
                  _                        -> err $ GenericError "Expected an interval binder"
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

    (P.Lam x ann t, VLine a) -> do
      case ann of P.LANone                 -> pure ()
                  P.LAAnn (P.unPos -> P.I) -> pure ()
                  P.LADesugared{}          -> pure ()
                  _                        -> err $ GenericError "Expected an interval binder"
      t <- bindI x \r -> check t (a ∙ IVar r)
      pure $ LLam x t

    (P.Pair t u, VSg a b) -> do
      t <- check t a
      u <- check u (b ∙ eval t)
      pure $! Pair (b^.name) t u

    (P.GlueTm base eqs ts, VGlueTy a equivs) -> do
      ~eqs <- case eqs of
        Nothing -> pure (quote equivs)
        Just eqs -> do
          eqs <- elabSys (equivInto a) eqs
          pure eqs
      base <- check base a
      ts   <- elabGlueTmSys base ts a (equivs^.body)
      pure $ Glue base eqs ts

    -- inferring non-dependent motive for case
    (P.Case t Nothing cs, b) -> do
      Infer t a <- infer t
      case frc a of
        VTyCon typeinfo params -> do
          let qb = bind "_" a (quote a) \_ -> quote b
          let bv = NCl "_" $ CConst b
          frz <- readIORef $ typeinfo^.frozen
          unless frz $ err $ GenericError "Can't case split on the type that's being defined"
          cons <- readIORef $ typeinfo^.constructors
          cs <- elabCases params bv (LM.elems cons) cs
          pure $ Case t "_" qb cs
        VHTyCon inf params -> do
          let qb = bind "_" a (quote a) \_ -> quote b
          let bv = NCl "_" $ CConst b
          frz <- readIORef (inf^.frozen)
          unless frz $ err $ GenericError "Can't case split on the type that's being defined"
          cons <- LM.elems <$!> readIORef (inf^.constructors)
          cs <- elabHCases params bv cons cs CSNil
          pure $ HCase t "_" qb cs
        _ ->
          err $ ExpectedInductiveType (quote a)

    (P.Hole i p, a) -> do
      putStrLn ("HOLE ?" ++ maybe (sourcePosPretty ?srcPos) id i)
      showcxt <- getState <&> (^.printingOpts.showHoleCxts)
      let qa = quote a

      let showBinder :: PrettyArgs (Name -> String)
          showBinder "_" = '@':show ?dom
          showBinder x   = x

      let showIBinder :: PrettyArgs (Name -> String)
          showIBinder "_" = '@':show ?idom
          showIBinder x   = x

      let go :: PrettyArgs (RevLocals -> IO Tm)
          go = \case
            RLNil -> do
              when showcxt $ do
                putStrLn ("────────────────────────────────────────────────────────────")
              putStrLn (" : " ++ pretty qa ++ "\n")
              pure (Hole i p)
            RLBind x _ a ls -> do
              when showcxt $ putStrLn (showBinder x ++ " : " ++ pretty a)
              Pretty.bind x \_ -> go ls
            RLBindI x ls -> do
              when showcxt $ putStrLn (showIBinder x ++ " : I")
              Pretty.bindI x \_ -> go ls
            RLCof c ls -> do
              when showcxt $ putStrLn (pretty c)
              go ls

      withPrettyArgs0 $ go (revLocals ?locals)

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
          sp <- checkSp (dci^.name) ps sp (dci^.fieldTypes)
          pure $ DCon dci sp

        HDConHead dci sp -> do
          unless (dci^.tyConInfo.tyId == tyinf^.tyId) $ withPrettyArgs $
            err $ GenericError $
              "No such constructor for expected type:\n\n  "
              ++ pretty (quote (VTyCon tyinf ps))

          (!sp, !is) <- checkHSp (dci^.name) ps sp (dci^.fieldTypes) (dci^.ifields)

          pure $ HDCon dci (quoteParams ps) sp is

        TyConHead{} ->
          err $ GenericError $ withPrettyArgs $
            "Expected inductive type:\n\n  " ++ pretty (quote (VTyCon tyinf ps)) ++
            "\n\nbut the expression is a type constructor"

        HTyConHead{} ->
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
                                       "Hint: put a type annotation on the recursive definition."
      Just (TERec (Just inf)) -> SplitInfer <$!> inferSp (RecursiveCall inf) (inf^.recTyVal) sp
      Just (TEDCon inf)       -> pure $ DConHead inf sp
      Just (TEHDCon inf)      -> pure $ HDConHead inf sp
      Just (TEHTyCon inf)     -> pure $ HTyConHead inf sp

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
      Just (TERec Nothing) ->
        err $ GenericError $
            "Can't infer type for recursive call. "++
            "Hint: put a type annotation on the recursive definition."
      Just (TERec (Just inf)) ->
        SplitInfer <$!> inferSp (RecursiveCall inf) (inf^.recTyVal) sp
      Just (TEDef inf) ->
        SplitInfer <$!> inferSp (TopVar inf) (inf^.defTyVal) sp
      Just (TETyCon inf) ->
        pure $ TyConHead inf sp
      Just (TEHTyCon inf) ->
        pure $ HTyConHead inf sp
      Just (TEDCon{}) ->
        impossible
      Just (TEHDCon{}) ->
        impossible

  P.TopLvl x (Just y) -> do
    st <- getState
    case LM.lookup x (st^.top') of
      Nothing ->
        err $ GenericError $ "No type constructor with de Bruijn level"
      Just (TEDef _) ->
        err $ GenericError $ "No type constructor with de Bruijn level"
      Just TERec{} ->
        err $ GenericError $ "No type constructor with de Bruijn level"
      Just (TETyCon inf) -> do
        cons <- readIORef (inf^.constructors)
        case LM.lookup y cons of
          Nothing ->
            err $ GenericError $ "No data constructor with de Bruijn level"
          Just dinf ->
            pure $ DConHead dinf sp
      Just (TEHTyCon inf) -> do
        cons <- readIORef (inf^.constructors)
        case LM.lookup y cons of
          Nothing ->
            err $ GenericError $ "No data constructor with de Bruijn level"
          Just dinf ->
            pure $ HDConHead dinf sp
      Just TEDCon{} ->
        impossible
      Just TEHDCon{} ->
        impossible

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

checkSp :: Elab (Name -> Env -> [P.Tm] -> Tel -> IO Spine)
checkSp conname env sp fs = case (sp, fs) of
  (t:sp, TCons x a fs) -> do
    t  <- check t (evalIn env a)
    sp <- checkSp conname (EDef env (eval t)) sp fs
    pure $ SPCons t sp
  ([], TNil) ->
    pure $ SPNil
  (_:_, TNil) ->
    err $ GenericError $ "Constructor " ++ show conname ++ " applied to too many arguments"
  ([], TCons{}) ->
    err $ GenericError $ "Constructor " ++ show conname ++ " applied to too few arguments"

checkHSubSp :: Elab (Name -> [P.Tm] -> [Name] -> Sub -> IO Sub)
checkHSubSp conname ts is acc = case (ts, is) of
  ([], []) -> pure acc
  (t:ts, _:is) -> do
    i <- checkI t
    checkHSubSp conname ts is (acc `ext` i)
  (_:_, []) ->
    err $ GenericError $ "Constructor " ++ show conname ++ " applied to too many arguments"
  ([], _:_) ->
    err $ GenericError $ "Constructor " ++ show conname ++ " applied to too few arguments"

checkHSp :: Elab (Name -> Env -> [P.Tm] -> Tel -> [Name] -> IO (Spine, Sub))
checkHSp conname env sp fs is = case (sp, fs) of
  (t:sp, TCons x a fs) -> do
    t  <- check t (evalIn env a)
    (sp, is) <- checkHSp conname (EDef env (eval t)) sp fs is
    pure (SPCons t sp, is)
  (ts, TNil) -> do
    sub <- checkHSubSp conname ts is (emptySub (dom ?cof))
    pure (SPNil, sub)
  ([], TCons{}) ->
    err $ GenericError $ "Constructor " ++ show conname ++ " applied to too few arguments"

infer :: Elab (P.Tm -> IO Infer)
infer t = split t >>= \case

  -- no params + saturated
  DConHead inf sp -> case inf^.tyConInfo.paramTypes of
    TNil -> do
      sp <- checkSp (inf^.name) ENil sp (inf^.fieldTypes)
      pure $ Infer (DCon inf sp) (VTyCon (inf^.tyConInfo) ENil)
    _  ->
      err $ GenericError $ "Can't infer type for data constructor " ++ show (inf^.name) ++ " which has "
                            ++"type parameters"

  -- no params + saturated
  HDConHead inf sp -> case inf^.tyConInfo.paramTypes of
    TNil -> do
      (!sp, !sub) <- checkHSp (inf^.name) ENil sp (inf^.fieldTypes) (inf^.ifields)
      pure $ Infer (HDCon inf LSPNil sp sub) (VHTyCon (inf^.tyConInfo) ENil)
    _  ->
      err $ GenericError $ "Can't infer type for data constructor " ++ show (inf^.name) ++ " which has "
                            ++"type parameters"

  -- saturated
  TyConHead inf sp -> do
    sp <- checkSp (inf^.name) ENil sp (inf^.paramTypes)
    pure $ Infer (TyCon inf sp) VU

  -- saturated
  HTyConHead inf sp -> do
    sp <- checkSp (inf^.name) ENil sp (inf^.paramTypes)
    pure $ Infer (HTyCon inf sp) VU

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

  P.Lam x P.LANone t ->
    err CantInferLam

  P.Lam x P.LADesugared{} t ->
    impossible

  P.Lam x (P.LAAnn a) t -> case P.unPos a of
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
    sys <- elabSys (equivInto (eval a)) sys
    pure $! Infer (GlueTy a sys) VU

  P.GlueTm base (Just eqs) sys -> do
    Infer base a <- infer base
    eqs <- elabSys (equivInto a) eqs
    case evalSys eqs of
      VSTotal _ -> impossible
      VSNe veqs -> do
        sys <- elabGlueTmSys base sys a (veqs^.body)
        pure $! Infer (Glue base eqs sys) (VGlueTy a veqs)

  P.GlueTm _ Nothing _ -> do
    err CantInferGlueTm

  P.Unglue t -> do
    Infer t a <- infer t
    case frc a of
      VGlueTy a sys -> pure $! Infer (Unglue t (quote sys)) a
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
    case frc a of
      VTyCon tyinfo params -> do
        b <- bind x a (quote a) \_ -> check b VU
        let bv = makeNCl x b
        frz <- readIORef (tyinfo^.frozen)
        unless frz $ err $ GenericError "Can't case split on the type that's being defined"
        cons <- LM.elems <$!> readIORef (tyinfo^.constructors)
        cs <- elabCases params bv cons cs
        pure $! Infer (Case t x b cs) (bv ∙ eval t)
      VHTyCon inf params -> do
        b <- bind x a (quote a) \_ -> check b VU
        let bv = makeNCl x b
        frz <- readIORef (inf^.frozen)
        unless frz $ err $ GenericError "Can't case split on the type that's being defined"
        cons <- LM.elems <$!> readIORef (inf^.constructors)
        cs <- elabHCases params bv cons cs CSNil
        pure $! Infer (HCase t x b cs) (bv ∙ eval t)
      a ->
        err $ ExpectedInductiveType (quote a)

  P.Case _ Nothing _ ->
    err $ GenericError "Can't infer type for case expression"

  P.Split _ ->
    err $ GenericError "Can't infer type for case splitting function"

----------------------------------------------------------------------------------------------------

elabCase :: Elab (Env -> Tel -> Val -> [Name] -> P.Tm -> IO Tm)
elabCase tyenv fieldtypes rhstype xs body = case (fieldtypes, xs) of
  (TNil, []) ->
    check body rhstype
  (TCons _ a fieldtypes, x:xs) -> do
    let ~va = evalIn tyenv a
    bind x va (quote va) \x ->
      elabCase (EDef tyenv x) fieldtypes rhstype xs body
  _ -> do
    err $ GenericError "Wrong number of constructor fields"

caseLhsSp :: Lvl -> Tel -> VDSpine
caseLhsSp dom = \case
  TNil          -> VDNil
  TCons _ _ tel -> VDCons (vVar dom) (caseLhsSp (dom + 1) tel)

elabCases :: Elab (Env -> NamedClosure -> [DConInfo] -> [(Name, [Name], P.Tm)] -> IO Cases)
elabCases params b cons cs = case (cons, cs) of
  ([], []) ->
    pure CSNil
  (dci:cons, (x', xs, body):cs) | dci^.name == x' -> do
    let rhstype = b ∙ VDCon dci (caseLhsSp ?dom (dci^.fieldTypes))
    t  <- elabCase params (dci^.fieldTypes) rhstype xs body
    cs <- elabCases params b cons  cs
    pure $ CSCons (dci^.name) xs t cs
  _ ->
    err CaseMismatch

----------------------------------------------------------------------------------------------------

caseLhsIFields :: [Name] -> Sub -> Sub
caseLhsIFields xs acc = case xs of
  []   -> acc
  _:xs -> caseLhsIFields xs (liftSub acc)

evalBoundary :: EvalArgs (Sys -> NamedClosure -> EvalClosure Cases -> VSys)
evalBoundary bnd casety casecl = case bnd of
  SEmpty          -> vsempty
  SCons cof t bnd -> vscons (evalCof cof) (hcase (eval t) casety casecl)
                            (evalBoundary bnd casety casecl)

elabHCase' :: Elab (Env -> Sub -> [Name] -> Val -> [Name] -> NamedClosure
           -> EvalClosure Cases -> Sys -> P.Tm -> IO Tm)
elabHCase' params sub ifields rhstype xs ~casety ~casecl bnd body = case (ifields, xs) of
  ([], []) -> do
    t <- check body rhstype
    let vbnd = (let ?env = params; ?sub = sub; ?recurse = DontRecurse
                in evalBoundary bnd casety casecl)
    case vbnd of
      VSTotal v -> do
        conv (eval t) v
      VSNe (WIS sys _) -> do
        neSysCompat t sys
    pure t

  (_:ifields, x:xs) -> do
    bindI x \_ ->
      elabHCase' params (liftSub sub) ifields rhstype xs casety casecl bnd body
  _ ->
    err $ GenericError "Wrong number of constructor fields"

elabHCase :: Elab (Env -> Tel -> [Name] -> Val -> [Name] -> NamedClosure
          -> EvalClosure Cases -> Sys -> P.Tm -> IO Tm)
elabHCase params fieldtypes ifields rhstype xs ~casety ~casecl bnd body = case (fieldtypes, xs) of
  (TNil, []) -> do
    elabHCase' params (emptySub (dom ?cof)) ifields rhstype xs casety casecl bnd body
  (TCons _ a fieldtypes, x:xs) -> do
    let ~va = evalIn params a
    bind x va (quote va) \x ->
      elabHCase (EDef params x) fieldtypes ifields rhstype xs casety casecl bnd body
  _ -> do
    err $ GenericError "Wrong number of constructor fields"

elabHCases :: Elab (Env -> NamedClosure -> [HDConInfo] -> [(Name, [Name], P.Tm)] -> Cases -> IO Cases)
elabHCases params b cons cs prevCases = case (cons, cs) of
  ([], []) ->
    pure prevCases
  (dci:cons, (x', xs, body):cs) | dci^.name == x' -> do
    let lhsTm = HDCon dci (quoteParams params)
                          (quote (caseLhsSp ?dom (dci^.fieldTypes)))
                          (caseLhsIFields (dci^.ifields) (emptySub (dom ?cof)))
    let rhstype = b ∙ eval lhsTm
    let casecl  = EC (idSub (dom ?cof)) ?env DontRecurse prevCases
    t <- elabHCase params (dci^.fieldTypes)
                          (dci^.ifields)
                          rhstype xs b casecl (dci^.boundary) body
    elabHCases params b cons cs (snocCases prevCases x' xs t)
  _ ->
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
  LNil                      -> err $ GenericError $ "Interval variable not in scope: " ++ show x
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

neSysCompat :: Elab (Tm -> NeSys -> IO ())
neSysCompat t = \case
  NSEmpty       -> pure ()
  NSCons t' sys -> do (assumeCof (t'^.binds) (conv (eval t) (t'^.body)))
                      neSysCompat t sys

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

elabSys :: Elab (VTy -> P.Sys -> IO Sys)
elabSys componentTy = \case
  P.SEmpty ->
    pure SEmpty
  P.SCons cof t sys -> do
    cof <- checkCof cof
    let vcof = evalCof cof
    case vcof of
      VCTrue  -> err NonNeutralCofInSystem
      VCFalse -> err NonNeutralCofInSystem
      VCNe ncof _ -> do
        sys <- elabSys componentTy sys
        bindCof ncof do
          t <- check t componentTy
          sysCompat t sys
          pure $ SCons cof t sys

----------------------------------------------------------------------------------------------------

guardTopShadowing :: Elab (Name -> IO ())
guardTopShadowing x = do
  st <- getState
  case M.lookup x (st^.top) of
    Nothing             -> pure ()
    Just (TEDef inf  )  -> err $ TopShadowing (inf^.pos)
    Just (TETyCon inf)  -> err $ TopShadowing (inf^.pos)
    Just (TEDCon inf )  -> err $ TopShadowing (inf^.pos)
    Just (TEHTyCon inf) -> err $ TopShadowing (inf^.pos)
    Just (TEHDCon inf)  -> err $ TopShadowing (inf^.pos)
    Just (TERec _     ) -> impossible

elabTop :: P.Top -> IO ()
elabTop = \case

  P.TDef pos x ma t ptop -> withTopElab $ setPos pos do
    guardTopShadowing x

    l <- getState <&> (^.lvl)

    recInf <- case ma of
      Nothing ->
        pure Nothing
      Just a  -> do
        a <- check a VU
        let ~va = eval a
        pure $ Just $ RI l a va x (coerce pos)

    let recEntry = TERec recInf

    modState $
        (top  %~ M.insert x recEntry)
      . (top' %~ LM.insert l recEntry)
      . (lvl  +~ 1)

    (t, a, va) <- case recInf of
      Nothing  -> do {Infer t a <- infer t; pure (t, quote a, a)}
      Just inf -> do {t <- check t (inf^.recTyVal);
                      pure (t, inf^.recTy, inf^.recTyVal)}

    -- recursive evaluation
    let ~tv = (let ?sub = idSub (dom ?cof); ?recurse = Recurse (coerce tv)
               in Core.eval t)

    let defEntry = TEDef $ DI l t tv a va x (coerce pos)

    modState $
        (top  %~ M.insert x defEntry)
      . (top' %~ LM.insert l defEntry)

    elabTop ptop

  P.TImport pos modname ptop -> withTopElab $ setPos pos do
    st <- getState <&> (^.loadState)
    let dirpath = takeDirectory (st^.currentPath)
        newpath = dirpath </> (modname <.> "cctt")
    if S.member newpath (st^.loadedFiles) then do
      elabTop ptop
    else if elem newpath (st^.loadCycle) then do
      err $ ImportCycle (st^.currentPath) (st^.loadCycle)
    else do
      elabPath (Just pos) newpath
      elabTop ptop

  P.TData pos tyname ps cs ptop -> withTopElab $ setPos pos do
    guardTopShadowing tyname

    l       <- getState <&> (^.lvl)
    ps      <- elabTelescope ps
    consRef <- newIORef (mempty @(LM.Map DConInfo))
    frzRef  <- newIORef False

    let inf   = TCI l ps consRef frzRef tyname (coerce pos)
    let entry = TETyCon inf

    modState $
         (top  %~ M.insert tyname entry)
      .  (top' %~ LM.insert l entry)
      .  (lvl  +~ 1)

    bindTelescope ps $ elabConstructors inf 0 cs
    writeIORef frzRef True
    elabTop ptop

  P.THData pos tyname ps cs ptop -> withTopElab $ setPos pos do
    guardTopShadowing tyname

    l       <- getState <&> (^.lvl)
    ps      <- elabTelescope ps
    consRef <- newIORef (mempty @(LM.Map HDConInfo))
    frzRef  <- newIORef False

    let inf   = HTCI l ps consRef frzRef tyname (coerce pos)
    let entry = TEHTyCon inf

    modState $
         (top  %~ M.insert tyname entry)
      .  (top' %~ LM.insert l entry)
      .  (lvl  +~ 1)

    let tyConVal = VHTyCon inf (go ps 0 ENil) where
          go :: Tel -> Lvl -> Env -> Env
          go tel l acc = case tel of
            TNil          -> acc
            TCons _ _ tel -> go tel (l + 1) (EDef acc (vVar l))

    bindTelescope ps $ elabHConstructors inf tyConVal 0 cs
    writeIORef frzRef True
    elabTop ptop

  P.TEmpty ->
    pure ()

----------------------------------------------------------------------------------------------------

class IsCoherent a where
  isCoh :: a -> Bool

instance IsCoherent Tm where
  isCoh = \case
    TopVar{}         -> impossible
    RecursiveCall{}  -> impossible
    LocalVar{}       -> True
    Let{}            -> impossible
    TyCon{}          -> True
    DCon _ sp        -> isCoh sp
    HTyCon{}         -> True
    HDCon _ _ sp _   -> isCoh sp
    HCase{}          -> False
    HSplit{}         -> impossible
    Case{}           -> False
    Split{}          -> impossible
    Pi{}             -> True
    App{}            -> False
    Lam _ t          -> isCoh t
    Sg{}             -> True
    Pair _ t u       -> isCoh t && isCoh u
    Proj1{}          -> False
    Proj2{}          -> False
    Wrap{}           -> True
    Pack _ t         -> isCoh t
    Unpack{}         -> False
    U                -> True
    Path{}           -> True
    PApp{}           -> False
    PLam _ _ _ t     -> isCoh t
    Line{}           -> True
    LApp{}           -> False
    LLam _ t         -> isCoh t
    Coe{}            -> False
    HCom _ _ a sys t -> case a of HTyCon{} -> isCoh sys && isCoh t
                                  _        -> False
    GlueTy{}         -> True
    Glue t sys _     -> isCoh t && isCoh sys
    Unglue{}         -> False
    Hole{}           -> False
    Com{}            -> impossible
    WkI{}            -> impossible
    Refl{}           -> impossible
    Sym{}            -> impossible
    Trans{}          -> impossible
    Ap{}             -> impossible

instance IsCoherent Sys where
  isCoh = \case
    SEmpty          -> True
    SCons cof t sys -> isCoh t && isCoh sys

instance IsCoherent SysHCom where
  isCoh = \case
    SHEmpty            -> True
    SHCons cof x t sys -> isCoh t && isCoh sys

instance IsCoherent Spine where
  isCoh = \case
    SPNil       -> True
    SPCons t sp -> isCoh t && isCoh sp

elabHConstructors :: Elab (HTyConInfo -> Val -> Lvl -> [P.HConstructor] -> IO ())
elabHConstructors tyinf tyConVal conid = \case
  [] ->
    pure ()
  (pos, x, fs, bnd):cs -> setPos pos do
    guardTopShadowing x
    (fs, is) <- elabHTelescope fs
    (!bnd, !coh) <- bindTelescope fs $ bindIVars is do
      case bnd of
        Nothing  ->
          pure (SEmpty, True)
        Just sys -> do
          sys <- elabSys tyConVal sys
          case evalSys sys of
            VSTotal _         -> impossible
            VSNe (WIS nsys _) -> do
              let coh = isCoh (quote nsys)
              pure (sys, coh)

    let dinf = HDCI conid fs coh is bnd x tyinf (coerce pos)
    modState (top %~ M.insert x (TEHDCon dinf))
    modifyIORef' (tyinf^.constructors) (LM.insert conid dinf)
    elabHConstructors tyinf tyConVal (conid + 1) cs

elabConstructors :: Elab (TyConInfo -> Lvl -> [P.Constructor] -> IO ())
elabConstructors tyinf conid = \case
  [] ->
    pure ()
  (pos, x, fs):cs -> setPos pos do
    guardTopShadowing x
    fs <- elabTelescope fs
    let dinf = DCI conid fs x tyinf (coerce pos)
    modState (top %~ M.insert x (TEDCon dinf))
    modifyIORef' (tyinf^.constructors) (LM.insert conid dinf)
    elabConstructors tyinf (conid + 1) cs

elabHConIVars :: Elab ([(Name, P.Ty)] -> IO [Name])
elabHConIVars = \case
  []        -> pure []
  (x, a):ps -> frcPos a \case
    P.I -> (x:) <$!> elabHConIVars ps
    _   -> err $ GenericError "Expected an interval binder"

elabHTelescope :: Elab ([(Name, P.Ty)] -> IO (Tel, [Name]))
elabHTelescope = \case
  [] ->
    pure (TNil, [])
  (x, a):ps -> frcPos a \case
    P.I -> do
      is <- elabHConIVars ps
      pure (TNil, x:is)
    a -> do
      a <- check a VU
      bind x (eval a) a \_ -> do
        (ps, is) <- elabHTelescope ps
        pure (TCons x a ps, is)

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

bindIVars :: [Name] -> Elab a -> Elab a
bindIVars is act = case is of
  []   -> act
  x:is -> bindI x \_ -> bindIVars is act
{-# inline bindIVars #-}

----------------------------------------------------------------------------------------------------

elabPath :: Maybe (DontShow SourcePos) -> FilePath -> IO ()
elabPath pos path = do
  loadSt <- getState <&> (^.loadState)
  let oldpath  = loadSt^.currentPath
  let oldCycle = loadSt^.loadCycle
  let oldSrc   = loadSt^.currentSrc

  file <- readFile path `catch` \(e :: IOError) -> do
    case pos of
      Nothing -> do
        putStrLn $ "Can't open file: " ++ path
        exitSuccess
      Just pos -> withTopElab $ setPos pos do
        err $ CantOpenFile path

  (!top, !tparse) <- timed (parseString path file)
  modState $ (loadState.currentPath .~ path)
           . (loadState.loadCycle   .~ (path : oldCycle))
           . (parsingTime           +~ tparse)
           . (loadState.currentSrc  .~ file)
  top <- elabTop top
  modState $ (loadState.currentPath .~ oldpath)
           . (loadState.loadCycle   .~ oldCycle)
           . (loadState.currentSrc  .~ oldSrc)
           . (loadState.loadedFiles %~ S.insert path)
  pure top

elaborate :: FilePath -> IO ()
elaborate path = elabPath Nothing path `catch` \(e :: ErrInCxt) -> do
  displayErrInCxt e
  exitSuccess
