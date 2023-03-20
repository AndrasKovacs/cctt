
module Quotation where

import Interval
import Common
import CoreTypes
import Core

-- NOTE: every quote method expects forced arguments, except Val which forces its argument.
-- A sneaky complication is in NLApp where a forced NLApp t i does *not* imply that "i" is forced!
----------------------------------------------------------------------------------------------------

class Quote a b | a -> b where
  quote :: NCofArg => DomArg => a -> b

instance Quote I I where
  quote i = i; {-# inline quote #-}

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
    NGlue t s1 s2     -> Glue (quote t) (quote s1) (quote s2)
    NLApp t i         -> LApp (quote t) (quote (frc i))
    NElim mot ms t    -> Elim (quote mot) (quote ms) (quote t)

instance Quote Val Tm where
  quote t = case frc t of
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
    VTODO            -> TODO
    VLine t          -> Line (t^.name) (quote t)
    VLLam t          -> LLam (t^.name) (quote t)
    VTyCon x ts      -> TyCon x (quote ts)
    VDCon x i sp     -> DCon x i (quote sp)

instance Quote a b => Quote (BindCofLazy a) b where
  quote t = assumeCof (t^.binds) (quote (t^.body)); {-# inline quote #-}

instance Quote a b => Quote [a] [b] where
  quote = \case
    []   -> []
    a:as -> (:) $$! quote a $$! quote as
  {-# inline quote #-}

instance Quote VDSpine DSpine where
  quote = \case
    VDNil         -> DNil
    VDInd t sp    -> DInd (quote t) (quote sp)
    VDHInd t a sp -> DHInd (quote t) a (quote sp)
    VDExt t a sp  -> DExt (quote t) a (quote sp)

instance Quote a b => Quote (BindCof a) b where
  quote t = assumeCof (t^.binds) (quote (t^.body)); {-# inline quote #-}

instance Quote NeCof' Cof where
  quote (NeCof' _ c) = quote c
  {-# inline quote #-}

instance Quote VCof Cof where
  quote = \case
    VCTrue   -> CTrue
    VCFalse  -> impossible
    VCNe c _ -> quote c
  {-# inline quote #-}

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

instance Quote VMethods Methods where
  quote = \case
    VMNil          -> MNil
    VMCons xs t ms -> MCons xs (quoteMethod xs t) (quote ms)

instance Quote Env TyParams where
  quote = \case
    ENil       -> TPNil
    EDef env t -> TPSnoc (quote env) (quote t)

quoteMethod :: NCofArg => DomArg => [Name] -> EvalClosure -> Tm
quoteMethod xs (EC s e t) = case xs of
  []   -> let ?sub = s; ?env = e in quote (eval t)
  _:xs -> fresh \x -> quoteMethod xs (EC s (EDef e x) t)
