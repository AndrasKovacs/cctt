
module Quotation where

import Interval
import Substitution
import Common
import CoreTypes
import Core

----------------------------------------------------------------------------------------------------

class Quote a b | a -> b where
  quote :: NCofArg => DomArg => a -> b

instance Quote I I where
  quote = id; {-# inline quote #-}

instance Quote Ne Tm where
  quote n = case unSubNe n of
    NLocalVar x       -> LocalVar (lvlToIx ?dom x)
    NSub n s          -> impossible
    NApp t u          -> App (quote t) (quote u)
    NPApp t l r i     -> PApp (quote t) (quote l) (quote r) (quote i)
    NProj1 t          -> Proj1 (quote t)
    NProj2 t          -> Proj2 (quote t)
    NCoe r r' a t     -> Coe (quote r) (quote r') (a^.name) (quote a) (quote t)
    NHCom r r' a ts t -> HCom (quote r) (quote r') (quote a) (quote ts) (quote t)
    NUnglue t sys     -> Unglue (quote t) (quote sys)
    NGlue t sys       -> Glue (quote t) (quote sys)
    NNatElim p z s n  -> NatElim (quote p) (quote z) (quote s) (quote n)
    NLApp t i         -> LApp (quote t) (quote i)

instance Quote Val Tm where
  quote t = case unF (frc t) of
    VSub{}           -> impossible
    VNe n _          -> quote n
    VGlueTy a sys    -> GlueTy (quote a) (quote (fst sys))
    VPi a b          -> Pi (b^.name) (quote a) (quote b)
    VLam t           -> Lam (t^.name) (quote t)
    VPath a lhs rhs  -> Path (a^.name) (quote a) (quote lhs) (quote rhs)
    VPLam lhs rhs t  -> PLam (quote lhs) (quote rhs) (t^.name) (quote t)
    VSg a b          -> Sg (b^.name) (quote a) (quote b)
    VPair t u        -> Pair (quote t) (quote u)
    VU               -> U
    VNat             -> Nat
    VZero            -> Zero
    VSuc t           -> Suc (quote t)
    VTODO            -> TODO
    VLine t          -> Line (t^.name) (quote t)
    VLLam t          -> LLam (t^.name) (quote t)

instance Quote a b => Quote (BindCofLazy a) b where
  quote t = assumeCof (t^.binds) (quote (t^.body)); {-# inline quote #-}

instance Quote a b => Quote (BindCof a) b where
  quote t = assumeCof (t^.binds) (quote (t^.body)); {-# inline quote #-}

instance Quote NeCof' Cof where
  quote (NeCof' _ c) = quote c

instance Quote VCof Cof where
  quote = \case
    VCTrue   -> CTrue
    VCFalse  -> impossible
    VCNe c _ -> quote c

instance Quote NeCof Cof where
  quote c = go c CTrue where
    go c acc = case c of
      NCEq i j    -> CAnd (CofEq (quote i) (quote j)) acc
      NCAnd c1 c2 -> go c1 (go c2 acc)

instance (SubAction a, Quote a b) => Quote (BindI a) b where
  quote t = freshI \i -> quote (t ∙ IVar i); {-# inline quote #-}

instance (SubAction a, Quote a b) => Quote (BindILazy a) b where
  quote t = freshI \i -> quote (t ∙ IVar i); {-# inline quote #-}

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
  quote t = freshI \(IVar -> i) -> quote (t ∙ i); {-# inline quote #-}
