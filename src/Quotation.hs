
module Quotation where

import Cubical
import Common
import CoreTypes
import Core

-- Note: neutral inputs (NeSys, Ne, NeSysHCom) are assumed to be forced
--       other things are not!
----------------------------------------------------------------------------------------------------

class Quote a b | a -> b where
  quote :: NCofArg => DomArg => a -> b

instance Quote I I where
  quote i = frc i; {-# inline quote #-}

instance Quote Ne Tm where
  -- forced input
  quote n = case unSubNe n of
    NLocalVar x       -> LocalVar (lvlToIx ?dom x)
    NSub n s          -> impossible
    NApp t u          -> App (quote t) (quote u)
    NPApp t l r i     -> PApp (quote t) (quote l) (quote r) (quote i)
    NProj1 t x        -> Proj1 (quote t) x
    NProj2 t x        -> Proj2 (quote t) x
    NUnpack t x       -> Unpack (quote t) x
    NCoe r r' a t     -> Coe (quote r) (quote r') (a^.name) (quote a) (quote t)
    NUnglue t sys     -> Unglue (quote t) (quote sys)
    NLApp t i         -> LApp (quote t) (quote i)
    NDontRecurse x    -> RecursiveCall x
    NCase t b tag cs  -> Case (quote t) (b^.name) (quote b) tag (quoteCases cs)
    NHCase t b tag cs -> HCase (quote t) (b^.name) (quote b) tag (quoteHCases cs)

instance Quote Val Tm where
  quote t = case frc t of
    VSub{}               -> impossible
    VNe n _              -> quote n
    VGlueTy a sys        -> GlueTy (quote a) (quote sys)
    VGlue t eqs sys _    -> Glue (quote t) (quote eqs) (quote sys)
    VPi a b              -> Pi (b^.name) (quote a) (quote b)
    VLam t               -> Lam (t^.name) (quote t)
    VPath a lhs rhs      -> Path (a^.name) (quote a) (quote lhs) (quote rhs)
    VPLam lhs rhs t      -> PLam (quote lhs) (quote rhs) (t^.name) (quote t)
    VSg a b              -> Sg (b^.name) (quote a) (quote b)
    VPair x t u          -> Pair x (quote t) (quote u)
    VWrap x a            -> Wrap x (quote a)
    VPack x t            -> Pack x (quote t)
    VU                   -> U
    VHole h              -> Hole h
    VLine t              -> Line (t^.name) (quote t)
    VLLam t              -> LLam (t^.name) (quote t)
    VTyCon x ts          -> TyCon x (quote ts)
    VDCon ci sp          -> DCon ci (quote sp)
    VHTyCon i ts         -> HTyCon i (quote ts)
    VHDCon i ps fs s _   -> HDCon i (quoteParams ps) (quote fs) s
    VHCom r r' a sys t _ -> HCom (quote r) (quote r') (quote a) (quote sys) (quote t)

--------------------------------------------------------------------------------

quoteCases' :: EvalArgs (Cases -> Cases)
quoteCases' = \case
  CSNil               -> CSNil
  CSCons x xs body cs ->
    CSCons x xs
      (let (!env, !dom) = pushVars ?env xs in
       let ?env = env; ?dom = dom in
       quote (eval body))
      (quoteCases' cs)

-- We don't do recursive unfolding under Case binders
quoteCases :: NCofArg => DomArg => EvalClosure Cases -> Cases
quoteCases (EC sub env _ cs) =
  let ?sub = wkSub sub; ?env = env; ?recurse = DontRecurse in quoteCases' cs
{-# inline quoteCases #-}

quoteHCases' :: EvalArgs (HCases -> HCases)
quoteHCases' = \case
  HCSNil                  -> HCSNil
  HCSCons x xs is body cs ->
    HCSCons x xs is
      (let (!env, !dom) = pushVars ?env xs in
       let ?env = env; ?dom = dom in
       freshIVarsS is (quote (eval body)))
      (quoteHCases' cs)

-- We don't do recursive unfolding under Case binders
quoteHCases :: NCofArg => DomArg => EvalClosure HCases -> HCases
quoteHCases (EC sub env _ cs) =
  let ?sub = wkSub sub; ?env = env; ?recurse = DontRecurse in quoteHCases' cs
{-# inline quoteHCases #-}

quoteParams :: NCofArg => DomArg => Env -> LazySpine
quoteParams = go LSPNil where
  go acc = \case
    ENil       -> acc
    EDef env v -> go (LSPCons (quote v) acc) env

--------------------------------------------------------------------------------

instance Quote VDSpine Spine where
  quote = \case
    VDNil       -> SPNil
    VDCons t sp -> SPCons (quote t) (quote sp)

instance Quote a b => Quote (BindCofLazy a) b where
  quote t = assumeCof (t^.binds) (quote (t^.body)); {-# inline quote #-}

instance Quote a b => Quote [a] [b] where
  quote = \case
    []   -> []
    a:as -> (:) $$! quote a $$! quote as
  {-# inline quote #-}

instance Quote a b => Quote (BindCof a) b where
  quote t = assumeCof (t^.binds) (quote (t^.body)); {-# inline quote #-}

instance Quote a b => Quote (WithIS a) b where
  quote (WIS a _) = quote a
  {-# inline quote #-}

instance Quote NeCof Cof where
  quote (NCEq i j) = CEq (quote i) (quote j)

instance (SubAction a, Quote a b) => Quote (BindI a) b where
  quote t = freshI \i -> quote (t ∙ i); {-# inline quote #-}

instance (SubAction a, Quote a b) => Quote (BindILazy a) b where
  quote t = freshI \i -> quote (t ∙ i); {-# inline quote #-}

instance Quote NeSys Sys where
  quote = \case
    NSEmpty      -> SEmpty
    NSCons t sys -> SCons (quote (t^.binds)) (quote t) (quote sys)

instance Quote NeSysHCom SysHCom where
  quote = \case
    NSHEmpty      -> SHEmpty
    NSHCons t sys -> SHCons (quote (t^.binds)) (t^.body.name) (quote t) (quote sys)

instance Quote NamedClosure Tm where
  quote t = fresh \x -> quote (t ∙ x); {-# inline quote #-}

instance Quote NamedIClosure Tm where
  quote t = freshI \i -> quote (t ∙ i); {-# inline quote #-}

instance Quote Env Spine where
  quote = go SPNil where
    go acc = \case
      ENil       -> acc
      EDef env v -> go (SPCons (quote v) acc) env
