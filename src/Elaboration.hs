{-# options_ghc -Wno-unused-top-binds #-}

module Elaboration (elaborate) where

import Control.Exception
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import System.FilePath
import System.Directory
import System.Exit
import Data.List
import qualified Data.List.Split as List
import qualified Data.ByteString.Char8 as B

import Common hiding (debug)
import Core hiding (bindI, bindCof, define, eval, evalSys, evalBoundary)
import CoreTypes
import Cubical hiding (evalCof, evalI)
import Quotation
import ElabState
import Errors
import Parser

import qualified Common
import qualified Conversion
import qualified Core
import qualified Cubical
import qualified Presyntax as P
import qualified Data.LvlMap as LM

import Pretty hiding (bind, bindI)
import qualified Pretty

-- Wrapped functions
----------------------------------------------------------------------------------------------------

conv :: Elab (Val -> Val -> IO ())
conv t u = if Conversion.conv t u
  then pure ()
  else err $ CantConvert (quoteNoUnfold t) (quoteNoUnfold u)

convICl :: Elab (NamedIClosure -> NamedIClosure -> IO ())
convICl t u = if Conversion.conv t u
  then pure ()
  else err $ CantConvert (quoteNoUnfold t) (quoteNoUnfold u)

convExInf :: Elab (Val -> Val -> IO ())
convExInf t u = if Conversion.conv t u
  then pure ()
  else err $ CantConvertExInf (quoteNoUnfold t) (quoteNoUnfold u)

convNeCof :: Elab (NeCof -> NeCof -> IO ())
convNeCof c c' = if Conversion.conv c c'
  then pure ()
  else err $! CantConvertCof (quoteNoUnfold c) (quoteNoUnfold c')

convEndpoints :: Elab (Val -> Val -> IO ())
convEndpoints t u = if Conversion.conv t u
  then pure ()
  else err $ CantConvertEndpoints (quoteNoUnfold t) (quoteNoUnfold u)

convReflEndpoints :: Elab (Val -> Val -> IO ())
convReflEndpoints t u = if Conversion.conv t u
  then pure ()
  else err $ CantConvertReflEndpoints (quoteNoUnfold t) (quoteNoUnfold u)

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
evalCof cof = let ?sub = idSub (dom ?cof) in Cubical.evalCof cof

evalI :: NCofArg => I -> I
evalI i = let ?sub = idSub (dom ?cof) in Cubical.evalI i

debug :: PrettyArgs [String] -> Elab (IO ())
debug x = withPrettyArgs (Common.debug x)

setPos :: forall a b. P.Spanned a => a -> (PosArg => b) -> b
setPos a act = let ?srcPos = Box (P.leftPos a) in act
{-# inline setPos #-}

-- | Match on preterm, handle parens and lazily update the current position.
frcPTm :: P.Tm -> (PosArg => P.Tm -> a) -> PosArg => a
frcPTm t act = case t of
  P.Parens _ t _ -> frcPTm t act
  t              -> setPos t (act t)
{-# inline frcPTm #-}

-- | Create fibrant closure from term in extended context.
makeNCl :: Elab (Name -> Tm -> NamedClosure)
makeNCl x t = NCl x $ CEval $ EC (idSub (dom ?cof)) ?env DontRecurse t
{-# inline makeNCl #-}

----------------------------------------------------------------------------------------------------

data Infer = Infer Tm ~VTy deriving Show

data G = G {g1 :: Val, g2 :: Val} deriving Show
type GTy = G

gj :: Val -> G
gj v = G v v

gU = gj VU

-- TODO OPT: unbox
data Split
  = DConHead DConInfo [P.Tm]
  | TyConHead TyConInfo [P.Tm]
  | HTyConHead HTyConInfo [P.Tm]
  | HDConHead HDConInfo [P.Tm]
  | SplitInfer {-# unpack #-} Infer
  deriving Show

check :: Elab (P.Tm -> GTy -> IO Tm)
check t gtopA@(G topA ftopA) = frcPTm t \case

  P.Let _ (NSpan -> x) ma t u -> do
    (a, va, t) <- case ma of
      Nothing -> do
        Infer t va <- infer t
        pure (quoteNoUnfold va, va, t)
      Just a -> do
        a <- check a gU
        let ~va = eval a
        t <- check t (gj va)
        pure (a, va, t)
    let ~vt = eval t
    u <- define x va a vt $ check u gtopA
    pure $! Let x a t u

  P.HCom _ r r' Nothing sys t -> do
    r  <- checkI r
    r' <- checkI r'
    t  <- check t gtopA
    sys <- elabSysHCom topA r t sys
    pure $! HCom r r' (quoteNoUnfold topA) sys t

  t -> case (t, frcFull ftopA) of

    (P.Lam _ (bindToName -> x) ann t, VPi a b) -> do
      ~qa <- case ann of
        P.LANone         -> pure (quoteNoUnfold a)
        P.LAAnn a'       -> do a' <- check a' gU
                               conv (eval a') a
                               pure a'
        P.LADesugared a' -> check a' gU
      Lam x <$!> bind x a qa (\v -> check t (gj (b ∙ v)))

    (P.Split _ cs _, VPi a b) -> case frcFull a of
      VTyCon tyinfo params -> do
        frz <- readIORef (tyinfo^.frozen)
        unless frz $ err $ GenericError "Can't case split on the type that's being defined"
        cons <- readIORef (tyinfo^.constructors)
        cs <- elabCases params b (LM.elems cons) cs
        pure $! Split (b^.name) (quoteNoUnfold b) cs
      VHTyCon inf params -> do
        frz <- readIORef (inf^.frozen)
        unless frz $ err $ GenericError "Can't case split on the type that's being defined"
        cons <- readIORef (inf^.constructors)
        cs <- elabHCases params b (LM.elems cons) cs
        pure $! HSplit (b^.name) (quoteNoUnfold b) cs
      _ ->
        err $ ExpectedInductiveType (quoteNoUnfold a)

    (P.Lam _ bnd@(bindToName -> x) ann t, VPath a l r) -> do
      case ann of P.LANone                      -> pure ()
                  P.LAAnn (P.unParens -> P.I _) -> pure ()
                  P.LADesugared{}               -> pure ()
                  _                             -> setPos bnd $ err $ GenericError "Expected an interval binder"
      t <- bindI x \i -> check t (gj (a ∙ IVar i))
      convEndpoints (instantiate t I0) l
      convEndpoints (instantiate t I1) r
      pure $! PLam (quoteNoUnfold l) (quoteNoUnfold r) x t

    (P.PLam _ l r (bindToName -> x) t, VPath a l' r') -> do
      t <- bindI x \i -> check t (gj (a ∙ IVar i))
      convEndpoints (instantiate t I0) l'
      convEndpoints (instantiate t I1) r'
      l <- check l (gj (a ∙ I0))
      r <- check r (gj (a ∙ I1))
      convEndpoints (eval l) l'
      convEndpoints (eval r) r'
      pure $! PLam l r x t

    (P.Refl _ _, VPath a l r) -> do
      constantICl a
      convReflEndpoints l r
      pure $! Refl (quoteNoUnfold l)

    (P.Sym p _, VPath a y x) -> do
      constantICl a
      p <- check p (gj (VPath a x y))
      pure $! Sym (quoteNoUnfold (a ∙ I0)) (quoteNoUnfold x) (quoteNoUnfold y) p

    (P.Ap _ f p, VPath b fx fy) -> do
      constantICl b
      Infer p pty <- infer p
      (a, x, y) <- nonDepPath pty
      f <- check f (gj (fun (a ∙ I0) (b ∙ I0)))
      conv fx (eval f ∙ x)
      conv fy (eval f ∙ y)
      pure $! Ap f (quoteNoUnfold x) (quoteNoUnfold y) p

    (P.Trans p q, VPath a x z) -> do
      Infer p axy <- infer p
      (a', x', y) <- nonDepPath axy
      convICl a' a
      conv x' x
      q <- check q (gj (VPath a y z))
      pure $! Trans (quoteNoUnfold a) (quoteNoUnfold x) (quoteNoUnfold y) (quoteNoUnfold z) p q

    (P.Lam _ bnd@(bindToName -> x) ann t, VLine a) -> do
      case ann of P.LANone                      -> pure ()
                  P.LAAnn (P.unParens -> P.I _) -> pure ()
                  P.LADesugared{}               -> pure ()
                  _                             -> setPos bnd $ err $ GenericError "Expected an interval binder"
      t <- bindI x \r -> check t (gj (a ∙ IVar r))
      pure $ LLam x t

    (P.Pair t u, VSg a b) -> do
      t <- check t (gj a)
      u <- check u (gj (b ∙ eval t))
      pure $! Pair (b^.name) t u

    (P.GlueTm _ base eqs ts _, VGlueTy a equivs) -> do
      ~eqs <- case eqs of
        Nothing -> pure (quoteNoUnfold equivs)
        Just eqs -> do
          eqs <- elabSys (equivInto a) eqs
          pure eqs
      base <- check base (gj a)
      ts   <- elabGlueTmSys base ts a (equivs^.body)
      pure $ Glue base eqs ts

    -- inferring non-dependent motive for case
    (P.Case _ t Nothing cs _, b) -> do
      Infer t a <- infer t
      case frcFull a of
        VTyCon typeinfo params -> do
          let qb = bind N_ a (quoteNoUnfold a) \_ -> quoteNoUnfold b
          let bv = NCl N_ $ CConst b
          frz <- readIORef $ typeinfo^.frozen
          unless frz $ err $ GenericError "Can't case split on the type that's being defined"
          cons <- readIORef $ typeinfo^.constructors
          cs <- elabCases params bv (LM.elems cons) cs
          pure $ Case t N_ qb cs
        VHTyCon inf params -> do
          let qb = bind N_ a (quoteNoUnfold a) \_ -> quoteNoUnfold b
          let bv = NCl N_ $ CConst b
          frz <- readIORef (inf^.frozen)
          unless frz $ err $ GenericError "Can't case split on the type that's being defined"
          cons <- LM.elems <$!> readIORef (inf^.constructors)
          cs <- elabHCases params bv cons cs
          pure $ HCase t N_ qb cs
        _ ->
          err $ ExpectedInductiveType (quoteNoUnfold a)

    (P.Hole pos bnd, _) -> do

      let display :: Elab (VTy -> IO ())
          display a = do
             showcxt <- getState <&> (^.printingOpts.showHoleCxts)
             let qa = quoteNoUnfold a

             let showBinder :: PrettyArgs (Name -> String)
                 showBinder N_ = '@':show ?dom
                 showBinder x  = show x

             let showIBinder :: PrettyArgs (Name -> String)
                 showIBinder N_  = '@':show ?idom
                 showIBinder x   = show x

             let go :: PrettyArgs (RevLocals -> IO ())
                 go = \case
                   RLNil -> do
                     when showcxt $ do
                       putStrLn ("────────────────────────────────────────────────────────────")
                     putStrLn (" : " ++ pretty qa ++ "\n")
                   RLBind x va a ls -> do
                     let qa = quoteNoUnfold va
                     when showcxt $ putStrLn (showBinder x ++ " : " ++ pretty qa)
                     Pretty.bind x \_ -> go ls
                   RLBindI x ls -> do
                     when showcxt $ putStrLn (showIBinder x ++ " : I")
                     Pretty.bindI x \_ -> go ls
                   RLCof c ls -> do
                     when showcxt $ putStrLn (pretty c)
                     go ls

             withPrettyArgs0 $ go (revLocals ?locals)

      case bnd of
        Nothing             -> do let ppos = parsePos pos
                                  putStrLn ("HOLE ?"++show ppos)
                                  display topA
                                  pure (Hole (SrcHole SHUnnamed ppos))
        Just P.BDontBind{}  -> do let ppos = parsePos pos
                                  putStrLn ("HOLE ?"++show ppos)
                                  pure (Hole (SrcHole SHSilent ppos))
        Just (P.BName name) -> do let ~ppos = parsePos pos
                                  putStrLn ("HOLE ?"++show name)
                                  display topA
                                  pure (Hole (SrcHole (SHNamed (NSpan name)) ppos))

    (t, VWrap x a) -> do
      t <- check t (gj a)
      pure $! Pack x t

    (t, VTyCon tyinf ps) -> do
      split t >>= \case
        DConHead dci sp -> do
          unless (dci^.tyConInfo.tyId == tyinf^.tyId) $ withPrettyArgs $
            err $ GenericError $
              "No such constructor for expected type:\n\n  "
              ++ pretty (quoteNoUnfold (VTyCon tyinf ps))
          sp <- checkSp (dci^.name) ps sp (dci^.fieldTypes)
          pure $ DCon dci sp

        HDConHead{} ->
          err $ GenericError $ withPrettyArgs $
            "Expected inductive type:\n\n  " ++ pretty (quoteNoUnfold (VTyCon tyinf ps)) ++
            "\n\nbut the expression is a higher type constructor"

        TyConHead{} ->
          err $ GenericError $ withPrettyArgs $
            "Expected inductive type:\n\n  " ++ pretty (quoteNoUnfold (VTyCon tyinf ps)) ++
            "\n\nbut the expression is a type constructor"

        HTyConHead{} ->
          err $ GenericError $ withPrettyArgs $
            "Expected inductive type:\n\n  " ++ pretty (quoteNoUnfold (VTyCon tyinf ps)) ++
            "\n\nbut the expression is a type constructor"

        SplitInfer (Infer t a) -> do
          convExInf a topA
          pure t

    (t, VHTyCon tyinf ps) -> do
      split t >>= \case
        HDConHead dci sp -> do
          unless (dci^.tyConInfo.tyId == tyinf^.tyId) $ withPrettyArgs $
            err $ GenericError $
              "No such constructor for expected type:\n\n  "
              ++ pretty (quoteNoUnfold (VHTyCon tyinf ps))
          (!sp, !is) <- checkHSp (dci^.name) ps sp (dci^.fieldTypes) (dci^.ifields)
          pure $ HDCon dci (quoteParamsNoUnfold ps) sp is

        DConHead{} ->
          err $ GenericError $ withPrettyArgs $
            "Expected inductive type:\n\n  " ++ pretty (quoteNoUnfold (VHTyCon tyinf ps)) ++
            "\n\nbut the expression is a strict inductive type constructor"

        TyConHead{} ->
          err $ GenericError $ withPrettyArgs $
            "Expected inductive type:\n\n  " ++ pretty (quoteNoUnfold (VHTyCon tyinf ps)) ++
            "\n\nbut the expression is a type constructor"

        HTyConHead{} ->
          err $ GenericError $ withPrettyArgs $
            "Expected inductive type:\n\n  " ++ pretty (quoteNoUnfold (VHTyCon tyinf ps)) ++
            "\n\nbut the expression is a type constructor"

        SplitInfer (Infer t a) -> do
          convExInf a topA
          pure t

    (t, _) -> do
      Infer t a <- infer t
      convExInf a topA
      pure t

splitIdent :: Elab (Span -> Ix -> Locals -> [P.Tm] -> IO Split)
splitIdent x ix ls sp = case ls of

  LNil -> do
    st <- getState
    case M.lookup (spanToBs x) (st^.top) of
      Nothing                 -> err $ NameNotInScope x
      Just (TEDef inf)        -> SplitInfer <$!> inferSp (TopVar inf DontPrintTrace) (inf^.defTyVal) sp
      Just (TETyCon inf)      -> pure $ TyConHead inf sp
      Just (TERec Nothing)    -> err $ GenericError $
                                       "Can't infer type for recursive call. "++
                                       "Hint: put a type annotation on the recursive definition."
      Just (TERec (Just inf)) -> SplitInfer <$!> inferSp (RecursiveCall inf) (inf^.recTyVal) sp
      Just (TEDCon inf)       -> pure $ DConHead inf sp
      Just (TEHDCon inf)      -> pure $ HDConHead inf sp
      Just (TEHTyCon inf)     -> pure $ HTyConHead inf sp

  LBind ls x' a qa | NSpan x == x' -> SplitInfer <$!> inferSp (LocalVar ix) a sp
                   | True          -> splitIdent x (ix + 1) ls sp
  LBindI ls x'     | NSpan x == x' -> err UnexpectedI
                   | True          -> splitIdent x ix ls sp
  LCof ls _                        -> splitIdent x ix ls sp

goSplit :: Elab (P.Tm -> [P.Tm] -> P.Tm -> IO Split)
goSplit t sp topT = frcPTm t \case

  P.Ident x -> do
    splitIdent x 0 ?locals sp

  P.App t u -> do
    goSplit t (u:sp) topT

  P.TopLvl _ x Nothing _ -> do
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
        SplitInfer <$!> inferSp (TopVar inf DontPrintTrace) (inf^.defTyVal) sp
      Just (TETyCon inf) ->
        pure $ TyConHead inf sp
      Just (TEHTyCon inf) ->
        pure $ HTyConHead inf sp
      Just (TEDCon{}) ->
        impossible
      Just (TEHDCon{}) ->
        impossible

  P.TopLvl _ x (Just y) _ -> do
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
  u:sp -> case frcFull a of
    VPi a b -> do
      u <- check u (gj a)
      inferSp (App t u) (b ∙ eval u) sp
    VPath a l r -> do
      u <- checkI u
      inferSp (PApp (quoteNoUnfold l) (quoteNoUnfold r) t u) (a ∙ evalI u) sp
    VLine a -> do
      u <- checkI u
      inferSp (LApp t u) (a ∙ evalI u) sp
    _ ->
      err $! ExpectedPiPathLine (quoteNoUnfold a)

checkSp :: Elab (Name -> Env -> [P.Tm] -> Tel -> IO Spine)
checkSp conname env sp fs = case (sp, fs) of
  (t:sp, TCons x a fs) -> do
    t  <- check t (gj (evalIn env a))
    sp <- checkSp conname (EDef env (eval t)) sp fs
    pure $ SPCons t sp
  ([], TNil) ->
    pure $ SPNil
  (_:_, TNil) ->
    err $ OverAppliedCon (show conname)
  ([], TCons{}) ->
    err $ UnderAppliedCon (show conname)

checkHSubSp :: Elab (Name -> [P.Tm] -> [Name] -> Sub -> IO Sub)
checkHSubSp conname ts is acc = case (ts, is) of
  ([], []) -> pure acc
  (t:ts, _:is) -> do
    i <- checkI t
    checkHSubSp conname ts is (acc `ext` i)
  (_:_, []) ->
    err $ OverAppliedCon (show conname)
  ([], _:_) ->
    err $ UnderAppliedCon (show conname)

checkHSp :: Elab (Name -> Env -> [P.Tm] -> Tel -> [Name] -> IO (Spine, Sub))
checkHSp conname env sp fs is = case (sp, fs) of
  (t:sp, TCons x a fs) -> do
    t  <- check t (gj (evalIn env a))
    (sp, is) <- checkHSp conname (EDef env (eval t)) sp fs is
    pure (SPCons t sp, is)
  (ts, TNil) -> do
    sub <- checkHSubSp conname ts is (emptySub (dom ?cof))
    pure (SPNil, sub)
  ([], TCons{}) ->
    err $ UnderAppliedCon (show conname)

infer :: Elab (P.Tm -> IO Infer)
infer t = setPos t $ split t >>= \case

  -- no params + saturated
  DConHead inf sp -> case inf^.tyConInfo.paramTypes of
    TNil -> do
      sp <- checkSp (inf^.name) ENil sp (inf^.fieldTypes)
      pure $ Infer (DCon inf sp) (VTyCon (inf^.tyConInfo) ENil)
    _  ->
      err $ CantInferConParamTy (show (inf^.name))

  -- no params + saturated
  HDConHead inf sp -> case inf^.tyConInfo.paramTypes of
    TNil -> do
      (!sp, !sub) <- checkHSp (inf^.name) ENil sp (inf^.fieldTypes) (inf^.ifields)
      pure $ Infer (HDCon inf LSPNil sp sub) (VHTyCon (inf^.tyConInfo) ENil)
    _  ->
      err $ CantInferConParamTy (show (inf^.name))

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
inferNonSplit t = frcPTm t \case
  P.Parens{} -> impossible
  P.Ident{}  -> impossible
  P.TopLvl{} -> impossible
  P.App{}    -> impossible

  P.LocalLvl _ x _ -> do
    unless (0 <= x && x < ?dom) (err LocalLvlNotInScope)
    let ix = lvlToIx ?dom x
    let Box a = lookupLocalType ix ?locals
    pure $! Infer (LocalVar ix) a

  P.ILvl _ _ _ -> err UnexpectedI
  P.I0 _       -> err UnexpectedI
  P.I1 _       -> err UnexpectedI
  P.I _        -> err UnexpectedIType

  P.DepPath a t u -> do
    (x, a, _, src, tgt) <- elabBindMaybe a I0 I1
    t <- check t (gj src)
    u <- check u (gj tgt)
    pure $! Infer (Path x a t u) VU

  P.Let _ (NSpan -> x) ma t u -> do
    (a, va, t) <- case ma of
      Nothing -> do
        Infer t va <- infer t
        pure (quoteNoUnfold va, va, t)
      Just a -> do
        a <- check a gU
        let ~va = eval a
        t <- check t (gj va)
        pure (a, va, t)
    let ~vt = eval t
    Infer u b <- define x va a vt $ infer u
    pure $! Infer (Let x a t u) b

  P.Pi _ (bindToName -> x) (P.unParens -> P.I _) b -> do
    b <- bindI x \_ -> check b gU
    pure $ Infer (Line x b) VU

  P.Pi _ (bindToName -> x) a b -> do
    a <- check a gU
    b <- bind x (eval a) a \_ -> check b gU
    pure $ Infer (Pi x a b) VU

  P.PApp _ l r t u -> do
    Infer t a <- infer t
    case frcFull a of
      VPath a l' r' -> do
        u <- checkI u
        l <- check l (gj (a ∙I0))
        r <- check r (gj (a ∙ I1))
        convEndpoints l' (eval l)
        convEndpoints r' (eval r)
        pure $! Infer (PApp l r t u) (a ∙ evalI u)
      _ ->
        err $! ExpectedPath (quoteNoUnfold a)

  P.Lam _ x P.LANone t ->
    err CantInferLam

  P.Lam _ x P.LADesugared{} t ->
    impossible

  P.Lam _ (bindToName -> x) (P.LAAnn a) t -> case P.unParens a of
    -- line type
    P.I _ -> bindI x \i -> do
      Infer t a <- infer t
      pure $! Infer (LLam x t) (VLine $ NICl x $ ICBindI (BindI x i a))

    a -> do
      a <- eval <$!> check a gU
      (t, b, qb) <- bind x a (quoteNoUnfold a) \_ -> do
        Infer t b <- infer t
        let qb = quoteNoUnfold b
        pure (t, b, qb)
      pure $! Infer (Lam x t) (VPi a (makeNCl x qb))

  -- we infer non-dependent path types to explicit path lambdas.
  P.PLam _ l r (bindToName -> x) t -> do
    Infer l a <- infer l
    r <- check r (gj a)
    t <- bindI x \i -> check t (gj a)
    let vl = eval l
        vr = eval r
    convEndpoints vl (instantiate t I0)
    convEndpoints vr (instantiate t I1)
    pure $! Infer (PLam l r x t) (VPath (NICl x (ICConst a)) vl vr)

  P.Sg _ (bindToName -> x) a b -> do
    a <- check a gU
    b <- bind x (eval a) a \_ -> check b gU
    pure $ Infer (Sg x a b) VU

  P.Pair{} ->
    err CantInferPair

  P.Proj1 pt _ -> do
    Infer t a <- infer pt
    case frcFull a of
      VSg a b -> pure $ Infer (Proj1 t (b^.name)) a
      _       -> setPos pt $ err $! ExpectedSg (quoteNoUnfold a)

  P.Proj2 pt _ -> do
    Infer t a <- infer pt
    case frcFull a of
      VSg a b -> pure $! Infer (Proj2 t (b^.name)) (b ∙ proj1 (b^.name) (eval t))
      _       -> setPos pt $ err $! ExpectedSg (quoteNoUnfold a)

  P.Wrap p (bindToName -> x) a _ -> do
    a <- check a gU
    pure $! Infer (Wrap x a) VU

  P.ProjField t (NSpan -> x) -> do
    Infer t a <- infer t
    elabProjField x t (eval t) a

  P.U _ ->
    pure $ Infer U VU

  P.Path t u -> do
    Infer t a <- infer t
    u <- check u (gj a)
    pure $! Infer (Path N_ (Core.freshI \_ -> quoteNoUnfold a) t u) VU

  P.Coe _ r r' a t -> do
    r  <- checkI r
    r' <- checkI r'
    (x, a, va, src, tgt) <- elabBindMaybe a (evalI r) (evalI r')
    t <- check t (gj src)
    pure $! Infer (Coe r r' x a t) tgt

  P.HCom _ r r' Nothing sys t -> do
    r  <- checkI r
    r' <- checkI r'
    Infer t a <- infer t
    sys <- elabSysHCom a r t sys
    pure $! Infer (HCom r r' (quoteNoUnfold a) sys t) a

  P.HCom _ r r' (Just a) sys t -> do
    r   <- checkI r
    r'  <- checkI r'
    a   <- check a gU
    let va = eval a
    t   <- check t (gj va)
    sys <- elabSysHCom va r t sys
    pure $! Infer (HCom r r' a sys t) va

  P.GlueTy _ a sys _ -> do
    a   <- check a gU
    sys <- elabSys (equivInto (eval a)) sys
    pure $! Infer (GlueTy a sys) VU

  P.GlueTm _ base (Just eqs) sys _ -> do
    Infer base a <- infer base
    eqs <- elabSys (equivInto a) eqs
    case evalSys eqs of
      VSTotal _ -> impossible
      VSNe veqs -> do
        sys <- elabGlueTmSys base sys a (veqs^.body)
        pure $! Infer (Glue base eqs sys) (VGlueTy a veqs)

  P.GlueTm _ _ Nothing _ _ ->
    err CantInferGlueTm

  P.Unglue _ t -> do
    Infer t a <- infer t
    case frcFull a of
      VGlueTy a sys -> do
        pure $! Infer (Unglue t (quoteNoUnfold sys)) a
      _ ->
        err $! ExpectedGlueTy (quoteNoUnfold a)

  P.Com _ r r' a sys t -> do
    r  <- checkI r
    r' <- checkI r'
    (i, a, va, src, tgt) <- elabBindMaybe a (evalI r) (evalI r')
    t <- check t (gj src)
    -- NOTE: elabSysHCom happens to be correct for "com" as well. In the "hcom"
    -- case, the "a" type gets implicitly weakened under both a cof and an ivar
    -- binder when checking components. In the "com" case, "a" is already under
    -- an ivar binder, so it's only weakened under the cof. The boundary checks
    -- are exactly the same.
    sys <- elabSysHCom va r t sys
    pure $! Infer (Com r r' i a sys t) tgt

  P.Refl _ _  -> err CantInfer

  P.Sym p _ -> do
    Infer p axy <- infer p
    (a, x, y)   <- nonDepPath axy
    pure $! Infer (Sym (quoteNoUnfold a) (quoteNoUnfold x) (quoteNoUnfold y) p) (VPath a y x)

  P.Trans p q -> do
    Infer p axy <- infer p
    (a, x, y)   <- nonDepPath axy
    Infer q ayz <- infer q
    (a', y', z) <- nonDepPath ayz
    convICl a' a
    conv y' y
    pure $! Infer (Trans (quoteNoUnfold a) (quoteNoUnfold x) (quoteNoUnfold y) (quoteNoUnfold z) p q) (VPath a x z)

  P.Ap _ f p -> do
    Infer f ab <- infer f
    (a, b) <- nonDepFun ab
    Infer p axy <- infer p
    (a', x, y) <- nonDepPath axy
    bindI i_ \(IVar -> i) -> conv (a' ∙ i) a
    let vf = eval f
    pure $ Infer (Ap f (quoteNoUnfold x) (quoteNoUnfold y) p) (path (b ∙ x) (vf ∙ x) (vf ∙ y))

  P.Hole i _ ->
    err CantInferHole

  P.Case _ t (Just (bindToName -> x, b)) cs _ -> do
    Infer t a <- infer t
    case frcFull a of
      VTyCon tyinfo params -> do
        b <- bind x a (quoteNoUnfold a) \_ -> check b gU
        let bv = makeNCl x b
        frz <- readIORef (tyinfo^.frozen)
        unless frz $ err $ GenericError "Can't case split on the type that's being defined"
        cons <- LM.elems <$!> readIORef (tyinfo^.constructors)
        cs <- elabCases params bv cons cs
        pure $! Infer (Case t x b cs) (bv ∙ eval t)
      VHTyCon inf params -> do

        b <- bind x a (quoteNoUnfold a) \_ -> check b gU
        let bv = makeNCl x b
        frz <- readIORef (inf^.frozen)
        unless frz $ err $ GenericError "Can't case split on the type that's being defined"
        cons <- LM.elems <$!> readIORef (inf^.constructors)
        cs <- elabHCases params bv cons cs
        pure $! Infer (HCase t x b cs) (bv ∙ eval t)
      _ ->
        err $ ExpectedInductiveType (quoteNoUnfold a)

  P.Case p _ Nothing _ _ -> setPos p $
    err $ GenericError "Can't infer type for case expression"

  P.Split p _ _ -> setPos p $
    err $ GenericError "Can't infer type for case splitting function"


-- Inductive case
----------------------------------------------------------------------------------------------------

-- | The spine consisting of the last N bound vars, for each constructor field.
lhsSpine :: Elab (Tel -> VDSpine)
lhsSpine fs = go ?dom fs VDNil where
  go :: Lvl -> Tel -> VDSpine -> VDSpine
  go dom tel acc = case tel of
    TNil          -> acc
    TCons _ _ tel -> go (dom - 1) tel (VDCons (vVar (dom - 1)) acc)

elabCase :: Elab (Env -> DConInfo -> NamedClosure -> Tel -> [Name] -> P.Tm -> IO Tm)
elabCase params inf retty fieldtypes xs body = case (fieldtypes, xs) of
  (TNil, []) -> do
    let lhsval = VDCon inf (lhsSpine (inf^.fieldTypes))
    check body (gj (retty ∙ lhsval))
  (TCons _ a fieldtypes, x:xs) -> do
    let ~va = evalIn params a
    bind x va (quoteNoUnfold va) \x ->
      elabCase (EDef params x) inf retty fieldtypes xs body
  _ -> do
    err $ GenericError "Wrong number of constructor fields"

elabCases :: Elab (Env -> NamedClosure -> [DConInfo] -> [P.CaseItem] -> IO Cases)
elabCases params b cons cs = case (cons, cs) of
  ([], []) ->
    pure CSNil
  (dci:cons, (bnd@(bindToName -> x'), map bindToName -> xs, body):cs) | dci^.name == x' -> setPos bnd do
    t  <- elabCase params dci b (dci^.fieldTypes) xs body
    cs <- elabCases params b cons cs
    pure $ CSCons (dci^.name) xs t cs
  _ ->
    err CaseMismatch


-- HIT case
----------------------------------------------------------------------------------------------------

elabHCase' :: Elab (Env -> HDConInfo -> Env -> Sub -> [Name] -> [Name] -> NamedClosure -> P.Tm -> IO Tm)
elabHCase' params ~inf typarams sub ifields_ xs ~casety body = case (ifields_, xs) of
  ([], []) -> do
    let lhsval = hdcon inf typarams (lhsSpine (inf^.fieldTypes)) sub
    let rhsty  = casety ∙ lhsval
    check body (gj rhsty)
  (_:ifields, x:xs) -> do
    bindI x \_ ->
      elabHCase' params inf typarams (lift sub) ifields xs casety body
  _ -> do
    err $ GenericError "Wrong number of constructor fields"

elabHCase :: Elab (Env -> HDConInfo -> Tel -> [Name] -> [Name] -> NamedClosure -> P.Tm -> IO ([Name], [Name], Tm))
elabHCase params ~inf fieldtypes ifields xs ~casety body = case (fieldtypes, xs) of
  (TNil, xs) -> do
    t <- elabHCase' params inf params (emptySub (dom ?cof)) ifields xs casety body
    pure ([], xs, t)
  (TCons _ a fieldtypes, x:xs) -> do
    let ~va = evalIn params a
    bind x va (quoteNoUnfold va) \var -> do
      (xs, is, t) <- elabHCase (EDef params var) inf fieldtypes ifields xs casety body
      pure (x:xs, is, t)
  _ -> do
    err $ GenericError "Wrong number of constructor fields"

elabHCases' :: Elab (Env -> NamedClosure -> [HDConInfo] -> [P.CaseItem] -> IO HCases)
elabHCases' params b cons cs = case (cons, cs) of
  ([], []) ->
    pure HCSNil
  (dci:cons, (bnd@(bindToName -> x'), map bindToName -> xs, body):cs) | dci^.name == x' -> setPos bnd do
    (xs, is, t) <- elabHCase params dci (dci^.fieldTypes) (dci^.ifields) xs b body
    cs <- elabHCases' params b cons cs
    pure (HCSCons x' xs is t cs)
  _ ->
    err CaseMismatch

elabHCases :: Elab (Env -> NamedClosure -> [HDConInfo] -> [P.CaseItem] -> IO HCases)
elabHCases params b cons cs = do
  cs <- elabHCases' params b cons cs
  modState (hCaseBoundaryChecks %~ (HCBC params cons b cs:))
  pure cs

----------------------------------------------------------------------------------------------------

elabProjField :: Elab (Name -> Tm -> Val -> VTy -> IO Infer)
elabProjField x t ~tv a = case frcFull a of
  VSg a b    -> if x == b^.name then
                  pure (Infer (Proj1 t x) a)
                else
                  elabProjField x (Proj2 t (b^.name))
                                  (proj2 (b^.name) tv)
                                  (b ∙ proj1 (b^.name) tv)
  VWrap x' a -> if x == x' then
                  pure (Infer (Unpack t x) a)
                else
                  err $ NoSuchField x (quoteNoUnfold (VWrap x' a))
  _          -> err $ NoSuchField x (quoteNoUnfold a)

-- | Ensure that an IClosure is constant.
constantICl :: Elab (NamedIClosure -> IO ())
constantICl a = bindI i_ \(IVar -> i) -> bindI j_ \(IVar -> j) -> conv (a ∙ i) (a ∙ j)

-- | Ensure that a Closure is constant.
constantCl :: Elab (VTy -> NamedClosure -> IO ())
constantCl a cl = bind x_ a (quoteNoUnfold a) \x -> bind y_ a (quoteNoUnfold a) \y -> conv (cl ∙ x) (cl ∙ y)

-- | Ensure that a type is a non-dependent function.
nonDepFun :: Elab (Val -> IO (Val, NamedClosure))
nonDepFun a = case frcFull a of
  VPi a b -> constantCl a b >> pure (a, b)
  _       -> err $! ExpectedNonDepFun (quoteNoUnfold a)

-- | Ensure that a type is a non-dependent path type.
nonDepPath :: Elab (Val -> IO (NamedIClosure, Val, Val))
nonDepPath a = case frcFull a of
  VPath a x y -> constantICl a >> pure (a, x, y)
  a           -> err $! ExpectedPath (quoteNoUnfold a)

-- | Return binder name, type under binder, value of type under binder
--   , source type val, target type val
elabBindMaybe :: Elab (P.BindMaybe -> I -> I -> IO (Name, Tm, Val, Val, Val))
elabBindMaybe b r r' = case b of
  P.BMDontBind a -> do
    Infer a aty <- infer a
    case frcFull aty of
      VPath aty lhs rhs -> do
        isConstantU aty
        let va  = eval a
            src = papp lhs rhs va r
            tgt = papp lhs rhs va r'
        let iname = pickIVarName
        bindI iname \i -> do
          a <- pure $ PApp (quoteNoUnfold lhs) (quoteNoUnfold rhs) (WkI a) (IVar i)
          pure (iname, a, eval a, src, tgt)
      VLine aty -> do
        isConstantU aty
        let va  = eval a
            src = lapp va r
            tgt = lapp va r'
        let iname = pickIVarName
        bindI iname \i -> do
          a <- pure $ LApp (WkI a) (IVar i)
          pure (iname, a, eval a, src, tgt)
      _ -> do
        err $! ExpectedPathLine (quoteNoUnfold aty)

  P.BMBind (bindToName -> x) a -> do
    (a, va) <- bindI x \_ -> do {a <- check a gU; pure (a, eval a)}
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
checkI t = frcPTm t \case
  P.Parens{} -> impossible
  P.I0 _     -> pure I0
  P.I1 _     -> pure I1

  P.Ident x -> do
    identI (NSpan x) (dom ?cof) ?locals

  P.ILvl p x _ -> do
    unless (0 <= x && x < dom ?cof)
           (setPos p $ err $ GenericError "Interval level not in scope")
    pure $ IVar x

  P.LocalLvl p (coerce -> x) _ -> do
    unless (0 <= x && x < dom ?cof)
           (setPos p $ err $ GenericError "Interval level not in scope")
    pure $ IVar x

  t -> do
    err ExpectedI

isConstantU :: Elab (NamedIClosure -> IO ())
isConstantU t = bindI i_ \i ->
  let ty = t ∙ IVar i in
  case frcFull ty of
  VU -> pure ()
  _  -> err $ ExpectedPathULineU (quoteNoUnfold ty)

--------------------------------------------------------------------------------

checkCof' :: Elab (P.Cof -> IO Cof)
checkCof' (P.CEq i j) = CEq <$!> checkI i <*!> checkI j

checkCof :: Elab ([P.Cof] -> IO [Cof])
checkCof xs = traverse checkCof' xs


-- Systems
----------------------------------------------------------------------------------------------------

sysHComCompat :: Elab (Tm -> SysHCom -> IO ())
sysHComCompat t = \case
  SHEmpty              -> pure ()
  SHCons cof' x t' sys -> do
    case fmap evalCof cof' of
      [VCFalse]     -> pure ()
      [VCTrue]      -> bindI x \_ -> conv (eval t) (eval t')
      [VCNe cof' _] -> bindCof cof' (bindI x \_ -> conv (eval t) (eval t'))
    sysHComCompat t sys

elabSysHCom :: Elab (VTy -> I -> Tm ->  P.SysHCom -> IO SysHCom)
elabSysHCom a r base = \case
  P.SHEmpty ->
    pure SHEmpty
  P.SHCons pos cof t sys -> setPos pos do
    cof <- checkCof cof
    case fmap evalCof cof of
      [VCTrue]  -> err NonNeutralCofInSystem
      [VCFalse] -> err NonNeutralCofInSystem
      [VCNe ncof _] -> do
        sys <- elabSysHCom a r base sys
        bindCof ncof do

          -- desugar binders
          (x, t, raw_t) <- case t of
            P.BMBind (bindToName -> x) raw_t -> do
              t <- bindI x \_ -> check raw_t (gj a) -- "a" is weakened under vcof
              pure (x, t, raw_t)
            P.BMDontBind raw_t -> setPos raw_t do
              Infer t tty <- infer raw_t
              case frcFull tty of
                VPath pty lhs rhs -> do
                  let iname = pickIVarName
                  bindI iname \i -> do
                    conv (pty ∙ IVar i) a
                    t <- pure $ PApp (quoteNoUnfold lhs) (quoteNoUnfold rhs) (WkI t) (IVar i)
                    pure (iname, t, raw_t)
                VLine pty -> do
                  let iname = pickIVarName
                  bindI iname \i -> do
                    conv (pty ∙ IVar i) a
                    t <- pure $ LApp (WkI t) (IVar i)
                    pure (iname, t, raw_t)
                _ -> do
                  err $! ExpectedPathLine (quoteNoUnfold tty)

          setPos raw_t do
            conv (instantiate t (frc r)) (eval base) -- check compatibility with base
            sysHComCompat t sys                      -- check compatibility with rest of system
            pure $ SHCons cof x t sys


sysCompat :: Elab (Tm -> Sys -> IO ())
sysCompat t = \case
  SEmpty            -> pure ()
  SCons cof' t' sys -> do
    case fmap evalCof cof' of
      [VCTrue]      -> conv (eval t) (eval t')
      [VCFalse]     -> pure ()
      [VCNe cof' _] -> bindCof cof' $ conv (eval t) (eval t')
    sysCompat t sys

elabGlueTmSys :: Elab (Tm -> P.Sys -> VTy -> NeSys -> IO Sys)
elabGlueTmSys base ts a equivs = case (ts, equivs) of
  (P.SEmpty, NSEmpty) ->
    pure SEmpty
  (P.SCons cof t ts, NSCons (BindCofLazy cof' equiv) equivs) -> setPos cof do
    cof <- checkCof cof
    case fmap evalCof cof of
      [VCTrue]  -> err NonNeutralCofInSystem
      [VCFalse] -> err NonNeutralCofInSystem
      [VCNe ncof _] -> do
        convNeCof (ncof^.extra) cof'
        ts <- elabGlueTmSys base ts a equivs
        setPos t $ bindCof ncof do
          let fequiv = frcFull equiv
          t <- check t (gj (proj1 ty_ fequiv))
          conv (proj1 f_ (proj2 ty_ fequiv) ∙ eval t) (eval base)
          sysCompat t ts
          pure $ SCons cof t ts
  (ts, equivs) ->
    err $! GlueTmSystemMismatch (quoteNoUnfold equivs)

elabSys :: Elab (VTy -> P.Sys -> IO Sys)
elabSys componentTy = \case
  P.SEmpty ->
    pure SEmpty
  P.SCons cof t sys -> setPos cof do
    cof <- checkCof cof
    let vcof = fmap evalCof cof
    case vcof of
      [VCTrue]  -> err NonNeutralCofInSystem
      [VCFalse] -> err NonNeutralCofInSystem
      [VCNe ncof _] -> do
        sys <- elabSys componentTy sys
        setPos t $ bindCof ncof do
          t <- check t (gj componentTy)
          sysCompat t sys
          pure $ SCons cof t sys

----------------------------------------------------------------------------------------------------

guardTopShadowing :: Elab (Span -> IO ())
guardTopShadowing x = setPos x do
  st <- getState
  case M.lookup (spanToBs x) (st^.top) of
    Nothing             -> pure ()
    Just (TEDef inf  )  -> err $ TopShadowing (inf^.pos)
    Just (TETyCon inf)  -> err $ TopShadowing (inf^.pos)
    Just (TEDCon inf )  -> err $ TopShadowing (inf^.pos)
    Just (TEHTyCon inf) -> err $ TopShadowing (inf^.pos)
    Just (TEHDCon inf)  -> err $ TopShadowing (inf^.pos)
    Just (TERec _     ) -> impossible


-- HIT case boundary checking
----------------------------------------------------------------------------------------------------

evalHCaseBoundary :: EvalArgs (Sys -> NamedClosure -> EvalClosure HCases -> VSys)
evalHCaseBoundary bnd casety casecl = case bnd of
  SEmpty          -> vsempty
  SCons cof t bnd -> vscons (Cubical.evalCofs cof) (hcase (eval t) casety casecl)
                            (evalHCaseBoundary bnd casety casecl)

neSysCompat :: Elab (Recurse -> Tm -> NeSys -> IO ())
neSysCompat rc t = \case
  NSEmpty       -> pure ()
  NSCons t' sys -> do
    assumeCof (t'^.binds) do
      let lhs = (let ?recurse = rc; ?sub = idSub (dom ?cof) in Core.eval t)
      let rhs = t'^.body
      conv lhs rhs
    neSysCompat rc t sys

checkHCaseBoundary' :: Elab (   HDConInfo -> Recurse -> Env -> Sub
                             -> [Name] -> Tm -> NamedClosure -> EvalClosure HCases -> IO ())
checkHCaseBoundary' ~inf rc params sub is body casety casecl = case is of
  [] -> do
    let vbnd = (let ?env = params; ?sub = sub; ?recurse = rc
                in evalHCaseBoundary (inf^.boundary) casety casecl)

    case vbnd of
      VSTotal v        -> conv (eval body) v
      VSNe (WIS sys _) -> neSysCompat rc body sys

  x:is ->
    bindI x \_ -> checkHCaseBoundary' inf rc params (lift sub) is body casety casecl

checkHCaseBoundary :: Elab (  HDConInfo -> Recurse -> Env -> Sub -> Tel -> [Name] -> [Name]
                           -> Tm -> NamedClosure -> EvalClosure HCases -> IO ())
checkHCaseBoundary ~inf rc params sub fields fs is body casety casecl = case (fields, fs) of
  (TNil, []) ->
    checkHCaseBoundary' inf rc params sub is body casety casecl
  (TCons _ a fields, x:fs) -> do
    let ~va = evalIn params a
    bind x va (quoteNoUnfold va) \var ->
      checkHCaseBoundary inf rc (EDef params var) sub fields fs is body casety casecl
  _ ->
    impossible

checkHCaseBoundaries' :: Elab (   Recurse -> Env -> [HDConInfo] -> HCases
                               -> NamedClosure -> EvalClosure HCases -> IO ())
checkHCaseBoundaries' rc params cons cs casety casecl = case (cons, cs) of
  ([], HCSNil) ->
    pure ()
  (inf:cons, HCSCons _ fs is t cs) -> do
    checkHCaseBoundary inf rc params (emptySub (dom ?cof)) (inf^.fieldTypes) fs is t casety casecl
    checkHCaseBoundaries' rc params cons cs casety casecl
  _ ->
    impossible

checkHCaseBoundaries :: Elab (Recurse -> IO ())
checkHCaseBoundaries recurse = do
  st <- getState
  forM_ (st^.hCaseBoundaryChecks) \(HCBC params cons casety cs) -> do
    checkHCaseBoundaries' recurse params cons cs casety (EC (idSub (dom ?cof)) ?env recurse cs)
  putState (st & hCaseBoundaryChecks .~ [])

----------------------------------------------------------------------------------------------------

elabTop :: P.Top -> IO ()
elabTop = \case

  P.TDef pos x ma t ptop -> withTopElab $ setPos pos do
    guardTopShadowing x
    xn <- pure $ NSpan x

    l <- getState <&> (^.lvl)

    recInf <- case ma of
      Nothing ->
        pure Nothing
      Just a  -> do
        a <- check a gU
        let ~va = eval a
        pure $ Just $ RI l a va xn (coerce pos)

    let recEntry = TERec recInf

    modState $
        (top  %~ M.insert (spanToBs x) recEntry)
      . (top' %~ LM.insert l recEntry)
      . (lvl  +~ 1)

    (t, a, va) <- case recInf of
      Nothing  -> do {Infer t a <- infer t; pure (t, quoteNoUnfold a, a)}
      Just inf -> do {t <- check t (gj (inf^.recTyVal));
                      pure (t, inf^.recTy, inf^.recTyVal)}

    -- recursive evaluation
    let ~tv = (let ?sub = idSub (dom ?cof); ?recurse = Recurse (coerce tv)
               in Core.eval t)

    unfold <- getState <&> (^.unfolding)
    let defEntry = TEDef $ DI l t tv a va xn (coerce pos) unfold

    modState $
        (top  %~ M.insert (spanToBs x) defEntry)
      . (top' %~ LM.insert l defEntry)

    checkHCaseBoundaries (Recurse (coerce tv))
    elabTop ptop

  P.TImport pos modname ptop -> withTopElab $ setPos pos do
    st <- getState <&> (^.loadState)
    let modSuffix = dotsToSlashes modname <.> "cctt"
    let newpath = st^.basePath </> modSuffix
    if S.member newpath (st^.loadedFiles) then do
      elabTop ptop
    else if elem newpath (st^.loadCycle) then do
      err $ ImportCycle (st^.currentPath) (st^.loadCycle)
    else do
      elabPath (Just pos) newpath
      elabTop ptop

  P.TData pos tyname ps cs ptop -> withTopElab $ setPos pos do
    guardTopShadowing tyname
    tynamen <- pure $ NSpan tyname

    l       <- getState <&> (^.lvl)
    ps      <- elabTelescope ps
    consRef <- newIORef (mempty @(LM.Map DConInfo))
    frzRef  <- newIORef False

    let inf   = TCI l ps consRef frzRef tynamen (coerce pos)
    let entry = TETyCon inf

    modState $
         (top  %~ M.insert (spanToBs tyname) entry)
      .  (top' %~ LM.insert l entry)
      .  (lvl  +~ 1)

    bindTelescope ps $ elabConstructors inf 0 cs
    writeIORef frzRef True
    checkHCaseBoundaries DontRecurse
    elabTop ptop

  P.THData pos tyname ps cs ptop -> withTopElab $ setPos pos do
    guardTopShadowing tyname
    tynamen <- pure $ NSpan tyname

    l       <- getState <&> (^.lvl)
    ps      <- elabTelescope ps
    consRef <- newIORef (mempty @(LM.Map HDConInfo))
    frzRef  <- newIORef False

    let inf   = HTCI l ps consRef frzRef tynamen (coerce pos)
    let entry = TEHTyCon inf

    modState $
         (top  %~ M.insert (spanToBs tyname) entry)
      .  (top' %~ LM.insert l entry)
      .  (lvl  +~ 1)

    let tyConVal = VHTyCon inf (go ps 0 ENil) where
          go :: Tel -> Lvl -> Env -> Env
          go tel l acc = case tel of
            TNil          -> acc
            TCons _ _ tel -> go tel (l + 1) (EDef acc (vVar l))

    bindTelescope ps $ elabHConstructors inf tyConVal 0 cs
    writeIORef frzRef True
    checkHCaseBoundaries DontRecurse
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
  (x, fs, bnd):cs -> do
    guardTopShadowing x
    let xn = NSpan x
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
              let coh = isCoh (quoteNoUnfold nsys)
              pure (sys, coh)

    let dinf = HDCI conid fs coh is bnd xn tyinf (P.leftPos x)
    modState (top %~ M.insert (spanToBs x) (TEHDCon dinf))
    modifyIORef' (tyinf^.constructors) (LM.insert conid dinf)
    elabHConstructors tyinf tyConVal (conid + 1) cs

elabConstructors :: Elab (TyConInfo -> Lvl -> [P.Constructor] -> IO ())
elabConstructors tyinf conid = \case
  [] ->
    pure ()
  (x, fs):cs -> do
    guardTopShadowing x
    let xn = NSpan x
    fs <- elabTelescope fs
    let dinf = DCI conid fs xn tyinf (P.leftPos x)
    modState (top %~ M.insert (spanToBs x) (TEDCon dinf))
    modifyIORef' (tyinf^.constructors) (LM.insert conid dinf)
    elabConstructors tyinf (conid + 1) cs

elabHConIVars :: Elab ([(P.Bind, P.Ty)] -> IO [Name])
elabHConIVars = \case
  []        -> pure []
  (bindToName -> x, a):ps -> frcPTm a \case
    P.I _ -> (x:) <$!> elabHConIVars ps
    _     -> err $ GenericError "Expected an interval binder"

elabHTelescope :: Elab ([(P.Bind, P.Ty)] -> IO (Tel, [Name]))
elabHTelescope = \case
  [] ->
    pure (TNil, [])
  (bindToName -> x, a):ps -> frcPTm a \case
    P.I _ -> do
      is <- elabHConIVars ps
      pure (TNil, x:is)
    a -> do
      a <- check a gU
      bind x (eval a) a \_ -> do
        (ps, is) <- elabHTelescope ps
        pure (TCons x a ps, is)

elabTelescope :: Elab ([(P.Bind, P.Ty)] -> IO Tel)
elabTelescope = \case
  [] -> pure TNil
  (bindToName -> x, a):ps -> do
    a <- check a gU
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

dotsToSlashes :: String -> String
dotsToSlashes str = foldr (</>) "" (List.wordsBy (=='.') str)

elabPath :: Maybe Pos -> FilePath -> IO ()
elabPath pos path = do
  path <- makeAbsolute path

  loadSt <- getState <&> (^.loadState)
  let oldpath  = loadSt^.currentPath
  let oldCycle = loadSt^.loadCycle
  let oldSrc   = loadSt^.currentSrc

  file <- B.readFile path `catch` \(e :: IOError) -> do
    case pos of
      Nothing -> do
        putStrLn $ "Can't open file: " ++ path
        exitSuccess
      Just pos -> withTopElab $ setPos pos do
        err $ CantOpenFile path

  ((!moddecl, !top), !tparse) <- timed (parseByteString path file)

  base <- case moddecl of
    Nothing  -> pure $ takeDirectory path
    Just mod -> do
      let modSuffix = dotsToSlashes mod <.> "cctt"
      case reverse <$> stripPrefix (reverse modSuffix) (reverse path) of
        Nothing -> do
          putStrLn $ "Module name " ++ mod ++ " does not match file name"
          exitSuccess
        Just base ->
          pure base

  modState $ (loadState.currentPath .~ path)
           . (loadState.loadCycle   .~ (path : oldCycle))
           . (loadState.currentSrc  .~ file)
           . (loadState.basePath    .~ base)
           . (parsingTime           +~ tparse)

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
