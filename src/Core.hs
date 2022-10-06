{-# language UnboxedSums, UnboxedTuples #-}

module Core where

import Common
import Cube
import qualified IVarSet as IS


--------------------------------------------------------------------------------

-- GlueTy is an awkward mix between neutral and non-neutral:
--   - we match on it
--   - but it's not stable/canonical
-- Proposal:
--   - Have GlueTy in Val as another "neutral" case
--   - Thus we have overall 2 neutral cases

--------------------------------------------------------------------------------

type Name = String
type Ty = Tm

data Tm
  = TopVar Lvl ~(DontPrint Val)
  | LocalVar Ix
  | Let Name Tm Ty Tm

  | Pi Name Ty Ty
  | App Tm Tm
  | Lam Name Tm

  | Sg Name Ty Ty
  | Pair Tm Tm
  | Proj1 Tm
  | Proj2 Tm

  | U

  | PathP Name Ty Tm Tm         -- PathP i.A x y
  | PApp Tm Tm Tm I             -- (x : A i0)(y : A i1)(t : PathP i.A x y)(j : I)
  | PLam Name Tm

  | Coe I I Name Ty Tm          -- coe r r' i.A t
  | HCom I I Name Ty System Tm  -- hcom r r' i.A [α → t] u

  -- we switch the field orders here compared to the papers, because
  -- this one is the sensible "dependency" order

  | GlueTy Ty System            -- Glue A [α ↦ B]      (B : Σ X (A ≃ X))
  | GlueTm Tm System            -- glue a [α ↦ b]
  | Unglue Tm System            -- unglue g [α ↦ B]    (B : Σ X (A ≃ X))
  deriving Show

data System
  = SEmpty
  | SCons Cof Tm System
  deriving Show

--------------------------------------------------------------------------------

data VSystem
  = VSEmpty
  | VSCons Cof ~Val VSystem

data Ne
  = NLocalVar Lvl
  | NSub Ne Sub
  | NApp Ne Val
  | NPApp Ne Val Val IVar
  | NProj1 Ne
  | NProj2 Ne
  | NCoe I I Name VTy Val
  | NHCom I I Name VTy VSystem Val
  | NGlueTy VTy VSystem
  | NUnglue Val VSystem

data Env
  = ENil
  | EDef Env ~Val

type EnvArg = (?env :: Env)

data Closure
  = CEval Sub Env Tm
  | CCoePi I I Name VTy Closure Val

data IClosure
  = ICEval Sub Env Tm

type VTy = Val

data Val
  = VNe Ne IS.IVarSet
  | VSub Val Sub
  | VPi Name VTy Closure
  | VLam Name Closure
  | VPathP Name {-# unpack #-} IClosure Val Val
  | VPLam Name {-# unpack #-} IClosure
  | VSg Name VTy Closure
  | VPair Val Val
  | VU

type IDomArg = (?idom :: Lvl)
type DomArg  = (?dom  :: Lvl)

instance SubAction Val where
  sub v s = case v of
    VSub v s' -> VSub v (sub s' s)
    v         -> VSub v s

instance SubAction Ne where
  sub n s = case n of
    NSub n s' -> NSub n (sub s' s)
    n         -> NSub n s

instance SubAction Closure where

  -- note: recursive closure sub!! TODO: this is probably fine, but
  -- think about explicit Sub in Closure and forcing for Closure
  sub cl s = case cl of
    CEval s' env t      -> CEval (sub s' s) (sub env s) t
    CCoePi r r' i a b t -> CCoePi (sub r s) (sub r' s) i (sub a s) (sub b s) (sub t s)

instance SubAction IClosure where
  sub cl s = case cl of
    ICEval s' env t -> ICEval (sub s' s) (sub env s) t

instance SubAction Env where
  sub e s = case e of
    ENil     -> ENil
    EDef e v -> EDef (sub e s) (sub v s)

--------------------------------------------------------------------------------

localVar :: EnvArg => Ix -> Val
localVar x = go ?env x where
  go (EDef _ v) 0 = v
  go (EDef e _) x = go e (x - 1)
  go _          _ = impossible

coeFill :: IDomArg => I -> I -> Val -> Val -> Val
coeFill r r' a t = uf

coeFillBack :: IDomArg => I -> I -> Val -> Val -> Val
coeFillBack r r' a t = uf

capp :: IDomArg => NCofArg => DomArg => Closure -> Val -> Val
capp t u = case t of

  CEval s env t ->
    let ?sub = s; ?env = EDef env u in eval t

  CCoePi r r' i a b t ->
    coe r r' i(capp b (coeFillBack r r' a u))
              (app t (coe r' r i a u))

-- coeⁱ r r' ((a : A) → B a) t =
--   (λ (a' : A r'). coeⁱ r r' (B (coeFill⁻¹ⁱ r r' A a')) (t (coeⁱ r' r A a')))


app :: IDomArg => NCofArg => DomArg => Val -> Val -> Val
app t u = case t of
  VLam _ t -> capp t u
  VNe t is -> VNe (NApp t u) is
  _        -> impossible

proj1 :: Val -> Val
proj1 t = case t of
  VPair t _ -> t
  VNe t is  -> VNe (NProj1 t) is
  _         -> impossible

proj2 :: Val -> Val
proj2 t = case t of
  VPair _ u -> u
  VNe t is  -> VNe (NProj2 t) is
  _         -> impossible

icapp :: IDomArg => NCofArg => DomArg => IClosure -> I -> Val
icapp t i = case t of
  ICEval s env t -> let ?env = env; ?sub = snocSub s i in eval t

papp :: IDomArg => NCofArg => DomArg => Val -> Val -> Val -> I -> Val
papp ~t ~u0 ~u1 i = case i of
  I0     -> u0
  I1     -> u1
  IVar x -> case t of
    VPLam _ t -> icapp t (IVar x)
    VNe t is  -> VNe (NPApp t u0 u1 x) (IS.insert x is)
    _         -> impossible
{-# inline papp #-}

bindI :: (IDomArg => SubArg => NCofArg => a)
      -> (IDomArg => SubArg => NCofArg => a)
bindI act = let ?idom = ?idom + 1
                ?sub  = liftSub ?sub
                ?cof  = liftSub ?cof
            in act
{-# inline bindI #-}

coe :: IDomArg => NCofArg => DomArg => I -> I -> Name -> Val -> Val -> Val
coe r r' i a t = case a of

  _ | r == r'  -> t

  VPi x a b    -> VLam x (CCoePi r r' i a b t)

  VSg x a b    -> let t1 = proj1 t; t2 = proj2 t
                  in VPair (coe r r' i a t1)
                           (coe r r' i (capp b (coeFill r r' a t1)) t2)

  VU           -> uf

  a@(VNe n is) -> case forceNe n of
    NGlueTy b sys -> uf
    n             ->


    -- VNe (NCoe r r' i a t) (insertI r $ insertI r' is)



  VSub{}       -> impossible



-- coeⁱ r r' ((a : A) × B a) t =
--   (coeⁱ r r' A t.1, coeⁱ r r' (B (coeFillⁱ r r' A t.1)) t.2)

--   | r == r' = t
-- coe r r' x a t = case a of
--   VPi x a b -> uf


hcom :: IDomArg => NCofArg => DomArg => I -> I -> Name -> Val -> VSystem -> Val -> Val
hcom r r' x ~a ~t ~b = uf

evalI :: SubArg => NCofArg => I -> I
evalI i = i `sub` ?sub `sub` ?cof

evalSystem :: IDomArg => SubArg => NCofArg => DomArg => EnvArg =>
              System -> VSystem
evalSystem = uf

glueTy :: Val -> VSystem -> Val
glueTy = uf

glueTm :: Val -> VSystem -> Val
glueTm = uf

unglue :: Val -> VSystem -> Val
unglue = uf

eval :: IDomArg => SubArg => NCofArg => DomArg => EnvArg => Tm -> Val
eval = \case
  TopVar _ v        -> coerce v
  LocalVar x        -> localVar x
  Let x _ t u       -> let ~v = eval t in let ?env = EDef ?env v in eval u
  Pi x a b          -> VPi x (eval a) (CEval ?sub ?env b)
  App t u           -> app (eval t) (eval u)
  Lam x t           -> VLam x (CEval ?sub ?env t)
  Sg x a b          -> VSg x (eval a) (CEval ?sub ?env b)
  Pair t u          -> VPair (eval t) (eval u)
  Proj1 t           -> proj1 (eval t)
  Proj2 t           -> proj2 (eval t)
  U                 -> VU
  PathP x a t u     -> VPathP x (ICEval ?sub ?env a) (eval t) (eval u)
  PApp t u0 u1 i    -> papp (eval t) (eval u0) (eval u1) (sub i ?sub)
  PLam x t          -> VPLam x (ICEval ?sub ?env t)
  Coe r r' x a t    -> coe (evalI r) (evalI r') x (bindI (eval a)) (eval t)
  HCom r r' x a t b -> hcom (evalI r) (evalI r') x (eval a) (bindI (evalSystem t)) (eval b)
  GlueTy a sys      -> glueTy (eval a) (evalSystem sys)
  GlueTm t sys      -> glueTm (eval t) (evalSystem sys)
  Unglue t sys      -> unglue (eval t) (evalSystem sys)

force :: IDomArg => NCofArg => DomArg => Val -> Val
force = \case
  VSub v s     -> let ?sub = s in force' v
  v@(VNe t is) -> if isBlocked is then v else forceNe t
  v            -> v
{-# inline force #-}

forceI :: NCofArg => I -> I
forceI i = sub i ?cof

forceI' :: SubArg => NCofArg => I -> I
forceI' i = i `sub` ?sub `sub` ?cof

forceIVar :: NCofArg => IVar -> I
forceIVar x = lookupSub x ?cof

forceIVar' :: SubArg => NCofArg => IVar -> I
forceIVar' x = lookupSub x ?sub `sub` ?cof

force' :: IDomArg => SubArg => NCofArg => DomArg => Val -> Val
force' = \case
  VSub v s       -> impossible
  VNe t is       -> if isBlocked' is
                      then VNe (sub t ?sub) (sub is ?sub)
                      else forceNe' t
  VPi x a b      -> VPi x (sub a ?sub) (sub b ?sub)
  VLam x t       -> VLam x (sub t ?sub)
  VPathP x a t u -> VPathP x (sub a ?sub) (sub t ?sub) (sub u ?sub)
  VPLam x t      -> VPLam x (sub t ?sub)
  VSg x a b      -> VSg x (sub a ?sub) (sub b ?sub)
  VPair t u      -> VPair (sub t ?sub) (sub u ?sub)
  VU             -> VU

forceNe :: IDomArg => NCofArg => DomArg => Ne -> Val
forceNe = \case
  n@(NLocalVar x)      -> VNe n mempty
  NSub n s             -> let ?sub = s in forceNe' n
  NApp t u             -> app (forceNe t) u
  NPApp t l r i        -> papp (forceNe t) l r (forceIVar i)
  NProj1 t             -> proj1 (forceNe t)
  NProj2 t             -> proj2 (forceNe t)
  NCoe r r' x a t      -> coe (forceI r) (forceI r') x uf (force t)
  NHCom r r' x a sys t -> uf
  NGlueTy a sys        -> uf
  NUnglue t sys        -> uf

forceNe' :: IDomArg => SubArg => NCofArg => DomArg => Ne -> Val
forceNe' = \case
  n@(NLocalVar x)      -> VNe n mempty
  NSub n s             -> let ?sub = sub s ?sub in forceNe' n
  NApp t u             -> app (forceNe' t) (sub u ?sub)
  NPApp t l r i        -> papp (forceNe' t) (sub l ?sub) (sub r ?sub)
                               (forceIVar' i)
  NProj1 t             -> proj1 (forceNe' t)
  NProj2 t             -> proj2 (forceNe' t)
  NCoe r r' x a t      -> coe (forceI' r) (forceI' r') x uf (force' t)
  NHCom r r' x a sys t -> uf
  NGlueTy a sys        -> uf
  NUnglue t sys        -> uf
