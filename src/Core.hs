
module Core where

import qualified IVarSet as IS
import Common
import Interval
import Substitution

{-

--------------------------------------------------------------------------------

We adapt ordinary NbE to CTT, with explicit call-by-name interval
substitutions.

In ordinary NbE
- we have terms in a var context, t : Tm Γ A
- semantic values have closures instead of binders
- eval has type:
    (Γ Δ : Con)(env : ValSub Γ Δ)(A : Ty Δ) (t : Tm Δ A) → Val Γ (evalTy env A)
  where evalTy evaluates types, but usually we only have "eval", because of
  Russell universes and weak typing of definitions. In the simplest case, we
  only pass "env" and "t" as arguments and nothing else. In some impls, we might
  also want to pass "Γ" as well, which makes it possible to create "fresh"
  variables during evaluation.
- we store (env : ValSub Γ Δ) and (t : Tm (Δ,A) B) in a closure.

In CTT we have terms in a triple context consisting of
 - interval var context
 - a cofibration
 - a fibrant var context
written as ψ|α|Γ, with t : Tm (ψ|α|Γ) A

In ordinary TT NbE, environments are semantic context morphisms ("ValSub").  We
try to do the same in CTT. Informally, a morphism between ψ|α|Γ and ψ'|α'|Γ'
consists of
 - an interval substitution σ : ISub ψ ψ'
 - a cof morphism δ : α ⇒ α'[σ]
 - a substitution ν : ValSub Γ (Γ'[σ,δ])

The full type of eval is:

  eval : ∀ ψ α Γ π' α' Γ' (σ : ISub ψ ψ')(δ : α ⇒ α'[σ])(ν : ValSub Γ (Γ'[σ,δ]))
           (A : Ty (ψ'|α'|Γ'))
           (t : Tm (ψ'|α'|Γ') A)
         → Val (ψ|α|Γ) (eval A)

Now, what's actually relevant from this? We only pass the following data:

  ψ α Γ σ ν t

- ψ is given as a natural number size. It is used to get fresh ivars in
  filling operations.
- α is needed in forcing (see later)
- Γ is given as a size, it's used to distinguish closed and open evaluation;
  Γ=0 marks the closed case.
- σ,ν,t are needed in evaluation


-- Evaluation, substitution, forcing
--------------------------------------------------------------------------------

- Evaluation:   Env  -> Tm  -> Val.

- Substitution: ISub -> Val -> Val. Substitutes ivars. It *does not* perform any
  expensive operation, it only stores an explicit substitution into values. It does
  compose explicit substitutions eagerly.

- Forcing: Env -> Val -> Val.
  Computes values to head normal form w.r.t. explicit substitution and
  cofibrations. It pushes subs down. It only does expensive computation on
  neutrals, where the following might happen:
    1. the sub that's being pushed down creates redexes in the neutral
    2. the current cofibration creates redexes in the neutral

  More detail on 2. Recall that in vanilla NbE, weakening of values comes for
  free, we can just use values under extra binders. In CTT, weakening of fibrant
  contexts is still free, but cofibration weakening is not. If I have a neutral
  value under some cof, it might not be neutral under a conjuncted cof.

  However, cofs are only every weakened! There's no general "substitution"
  operation with cof morphisms. For this reason, we don't want to explicitly
  store cofs; we only pass the "current" cof and do forcing on demand. We also
  don't have to store cofs in closures!

Semantic ops:
  - They assume that their inputs are forced!
  - coe/hcom have two flavors

-- neutrals
--------------------------------------------------------------------------------


-- coe, hcom
--------------------------------------------------------------------------------



--------------------------------------------------------------------------------

If we really want to do things nicely, we need 4 variations
for coe/hcom, and 2 variations for other semantic functions.

-}


-- Syntax
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

  | GlueTy Ty System            -- Glue A [α ↦ B]      (B : Σ X (X ≃ A))
  | GlueTm Tm System            -- glue a [α ↦ b]
  | Unglue Tm System            -- unglue g [α ↦ B]
  deriving Show

-- | Atomic equation.
data CofEq = CofEq I I
  deriving Show

-- | Conjunction of equations.
data Cof = CTrue | CAnd {-# unpack #-} CofEq Cof
  deriving Show

data System = SEmpty | SCons Cof Tm System
  deriving Show

-- Values
--------------------------------------------------------------------------------

data VSystem
  = VSEmpty
  | VSCons Cof ~Val VSystem

-- | An immediate result of system forcing. Marks the case where one branch is
--   true.
data FVSystem
  = FVSTakeBranch ~Val
  | FVSNeutral VSystem

newtype FVal  = FVal {unF :: Val} deriving SubAction
newtype FI    = FI   {unFI :: I}  deriving SubAction

data Ne
  = NLocalVar Lvl
  | NSub Ne Sub
  | NApp Ne Val
  | NPApp Ne Val Val IVar
  | NProj1 Ne
  | NProj2 Ne
  | NCoe I I Name VTy Val
  | NHCom I I Name VTy VSystem Val
  | NUnglue Val VSystem

data Env
  = ENil
  | EDef Env ~Val

type EnvArg = (?env :: Env)

-- | Defunctionalized closures.
data Closure
  = CEval Sub Env Tm                     -- ^ Body of vanilla term evaluation.
  | CCoePi FI FI Name VTy Closure FVal   -- ^ Body of function coercions.

-- | Defunctionalized closures for IVar abstraction.
data IClosure
  = ICEval Sub Env Tm

type VTy = Val

data Val
  = VSub Val Sub

  -- Neutrals. These are annotated with sets of blocking ivars.
  -- Glue types are also neutral, but they're handled separately, because we
  -- have to match on them in coe/hcom.
  | VNe Ne IS.IVarSet
  | VGlueTy VTy VSystem IS.IVarSet

  -- canonicals
  | VPi Name VTy Closure
  | VLam Name Closure
  | VPathP Name {-# unpack #-} IClosure Val Val
  | VPLam Name {-# unpack #-} IClosure
  | VSg Name VTy Closure
  | VPair Val Val
  | VU

type IDomArg = (?idom :: Lvl)
type DomArg  = (?dom  :: Lvl)


-- Substitution
--------------------------------------------------------------------------------

instance SubAction Val where
  sub v s = case v of
    VSub v s' -> VSub v (sub s' s)
    v         -> VSub v s

instance SubAction Ne where
  sub n s = case n of
    NSub n s' -> NSub n (sub s' s)
    n         -> NSub n s

instance SubAction Closure where
  sub cl s = case cl of
    CEval s' env t      -> CEval (sub s' s) (sub env s) t

    -- note: recursive closure sub! TODO to scrutinize, but this is probably
    -- fine, because recursive depth is bounded by Pi/Sigma type nesting.
    CCoePi r r' i a b t -> CCoePi (sub r s) (sub r' s) i (sub a s) (sub b s) (sub t s)

instance SubAction IClosure where
  sub cl s = case cl of
    ICEval s' env t -> ICEval (sub s' s) (sub env s) t

instance SubAction Env where
  sub e s = case e of
    ENil     -> ENil
    EDef e v -> EDef (sub e s) (sub v s)

instance SubAction CofEq where
  sub (CofEq i j) s = CofEq (sub i s) (sub j s)

instance SubAction Cof where
  sub cof s = case cof of
    CTrue       -> CTrue
    CAnd eq cof -> CAnd (sub eq s) (sub cof s)

instance SubAction VSystem where
  sub sys s = case sys of
    VSEmpty          -> VSEmpty
    VSCons cof v sys -> VSCons (sub cof s) (sub v s) (sub sys s)

--------------------------------------------------------------------------------



localVar :: EnvArg => Ix -> Val
localVar x = go ?env x where
  go (EDef _ v) 0 = v
  go (EDef e _) x = go e (x - 1)
  go _          _ = impossible

app :: IDomArg => NCofArg => DomArg => FVal -> Val -> Val
app t u = case unF t of
  VLam _ t -> capp t u
  VNe t is -> VNe (NApp t u) is
  _        -> impossible

-- | Apply a closure.
capp :: IDomArg => NCofArg => DomArg => Closure -> Val -> Val
capp t u = case t of

  CEval s env t ->
    let ?sub = s; ?env = EDef env u in eval t

  CCoePi r r' i a b t ->
    coe r r' i (force (capp b (coeFillInv r r' (force a) (force u))))
               (force (app t (coe r' r i (force a) (force u))))

-- | Apply an ivar closure.
icapp :: IDomArg => NCofArg => DomArg => IClosure -> I -> Val
icapp t i = case t of
  ICEval s env t -> let ?env = env; ?sub = snocSub s i in eval t

proj1 :: IDomArg => NCofArg => DomArg => FVal -> Val
proj1 t = case unF t of
  VPair t _ -> t
  VNe t is  -> VNe (NProj1 t) is
  _         -> impossible

proj2 :: IDomArg => NCofArg => DomArg => FVal -> Val
proj2 t = case unF t of
  VPair _ u -> u
  VNe t is  -> VNe (NProj2 t) is
  _         -> impossible

-- | Apply a path.
lazyPapp :: IDomArg => NCofArg => DomArg => FVal -> Val -> Val -> FI -> Val
lazyPapp ~t ~u0 ~u1 i = case unFI i of
  I0     -> u0
  I1     -> u1
  IVar x -> case unF t of
    VPLam _ t -> icapp t (IVar x)
    VNe t is  -> VNe (NPApp t u0 u1 x) (IS.insert x is)
    _         -> impossible
{-# inline lazyPapp #-}

coeFill :: IDomArg => FI -> FI -> FVal -> FVal -> Val
coeFill r r' a t = uf

coeFillInv :: IDomArg => FI -> FI -> FVal -> FVal -> Val
coeFillInv r r' a t = uf

coe :: IDomArg => NCofArg => DomArg => FI -> FI -> Name -> FVal -> FVal -> Val
coe r r' i a t = case unF a of
  VPi x a b ->
    VLam x (CCoePi r r' i a b t)

  VSg x (force -> a) b ->
    let t1 = force (proj1 t); t2 = force (proj2 t)
    in VPair (coe r r' i a t1)
             (coe r r' i (force (capp b (coeFill r r' a t1))) t2)

  VU -> uf

  a@(VNe n is) -> uf

  VSub{} ->
    impossible

  _ -> uf

lazyCoe :: IDomArg => NCofArg => DomArg => FI -> FI -> Name -> FVal -> FVal -> Val
lazyCoe r r' i ~a t
  | unFI r == unFI r' = unF t
  | True              = coe r r' i a t
{-# inline lazyCoe #-}

lazyHCom :: IDomArg => NCofArg => DomArg => FI -> FI -> Name -> FVal -> FVSystem -> FVal -> Val
lazyHCom r r' i ~a ~t ~b
  | unFI r == unFI r'    = unF b
  | FVSTakeBranch v <- t = v
  | FVSNeutral t    <- t = hcom r r' i a t b
{-# inline lazyHCom #-}

hcom :: IDomArg => NCofArg => DomArg => FI -> FI -> Name -> FVal -> VSystem -> FVal -> Val
hcom r r' x ~a ~t ~b = uf

evalI :: SubArg => NCofArg => I -> FI
evalI i = forceI (sub i ?sub)

evalSystem :: IDomArg => SubArg => NCofArg => DomArg => EnvArg =>
              System -> FVSystem
evalSystem = uf

lazyGlueTy :: Val -> FVSystem -> Val
lazyGlueTy = uf
{-# inline lazyGlueTy #-}

lazyGlueTm :: Val -> FVSystem -> Val
lazyGlueTm = uf
{-# inline lazyGlueTm #-}

lazyUnglue :: Val -> FVSystem -> Val
lazyUnglue = uf
{-# inline lazyUnglue #-}

bindI :: (IDomArg => SubArg => NCofArg => a)
      -> (IDomArg => SubArg => NCofArg => a)
bindI act = let ?idom = ?idom + 1
                ?sub  = liftSub ?sub
                ?cof  = liftSub ?cof
            in act
{-# inline bindI #-}

evalF :: IDomArg => SubArg => NCofArg => DomArg => EnvArg => Tm -> FVal
evalF t = force (eval t)
{-# inline evalF #-}

eval :: IDomArg => SubArg => NCofArg => DomArg => EnvArg => Tm -> Val
eval = \case
  TopVar _ v        -> coerce v
  LocalVar x        -> localVar x
  Let x _ t u       -> let ~v = eval t in let ?env = EDef ?env v in eval u
  Pi x a b          -> VPi x (eval a) (CEval ?sub ?env b)
  App t u           -> app (evalF t) (eval u)
  Lam x t           -> VLam x (CEval ?sub ?env t)
  Sg x a b          -> VSg x (eval a) (CEval ?sub ?env b)
  Pair t u          -> VPair (eval t) (eval u)
  Proj1 t           -> proj1 (evalF t)
  Proj2 t           -> proj2 (evalF t)
  U                 -> VU
  PathP x a t u     -> VPathP x (ICEval ?sub ?env a) (eval t) (eval u)
  PApp t u0 u1 i    -> lazyPapp (evalF t) (eval u0) (eval u1) (evalI i)
  PLam x t          -> VPLam x (ICEval ?sub ?env t)
  Coe r r' x a t    -> lazyCoe (evalI r) (evalI r') x (bindI (evalF a)) (evalF t)
  HCom r r' x a t b -> lazyHCom (evalI r) (evalI r') x (evalF a) (evalSystem t) (evalF b)
  GlueTy a sys      -> lazyGlueTy (eval a) (evalSystem sys)
  GlueTm t sys      -> lazyGlueTm (eval t) (evalSystem sys)
  Unglue t sys      -> lazyUnglue (eval t) (evalSystem sys)

forceSystem :: IDomArg => NCofArg => DomArg => VSystem -> FVSystem
forceSystem = uf

force :: IDomArg => NCofArg => DomArg => Val -> FVal
force = \case
  VSub v s             -> let ?sub = s in force' v
  v@(VNe t is)         -> if isBlocked is then FVal v else forceNe t
  v@(VGlueTy a sys is) -> if isBlocked is then FVal v else force (lazyGlueTy a (forceSystem sys))
  v                    -> FVal v

forceI :: NCofArg => I -> FI
forceI i = FI (sub i ?cof)

forceI' :: SubArg => NCofArg => I -> FI
forceI' i = FI (i `sub` ?sub `sub` ?cof)

forceIVar :: NCofArg => IVar -> FI
forceIVar x = FI (lookupSub x ?cof)

forceIVar' :: SubArg => NCofArg => IVar -> FI
forceIVar' x = FI (lookupSub x ?sub `sub` ?cof)

force' :: IDomArg => SubArg => NCofArg => DomArg => Val -> FVal
force' = \case
  VSub v s         -> impossible
  VNe t is         -> if isBlocked' is
                        then FVal (VNe (sub t ?sub) (sub is ?sub))
                        else forceNe' t
  VGlueTy a sys is -> if isBlocked' is
                        then FVal (VGlueTy (sub a ?sub) (sub sys ?sub) (sub is ?sub))
                        else uf
  VPi x a b        -> FVal (VPi x (sub a ?sub) (sub b ?sub))
  VLam x t         -> FVal (VLam x (sub t ?sub))
  VPathP x a t u   -> FVal (VPathP x (sub a ?sub) (sub t ?sub) (sub u ?sub))
  VPLam x t        -> FVal (VPLam x (sub t ?sub))
  VSg x a b        -> FVal (VSg x (sub a ?sub) (sub b ?sub))
  VPair t u        -> FVal (VPair (sub t ?sub) (sub u ?sub))
  VU               -> FVal VU

forceNe :: IDomArg => NCofArg => DomArg => Ne -> FVal
forceNe = \case
  n@(NLocalVar x)      -> FVal (VNe n mempty)
  NSub n s             -> let ?sub = s in forceNe' n
  NApp t u             -> force (app (forceNe t) u)
  NPApp t l r i        -> force (lazyPapp (forceNe t) l r (forceIVar i))
  NProj1 t             -> force (proj1 (forceNe t))
  NProj2 t             -> force (proj2 (forceNe t))
  NCoe r r' x a t      -> force (lazyCoe (forceI r) (forceI r') x uf (force t))
  NHCom r r' x a sys t -> force (lazyHCom (forceI r) (forceI r') x uf uf uf)
  NUnglue t sys        -> force (lazyUnglue t (forceSystem sys))

forceNe' :: IDomArg => SubArg => NCofArg => DomArg => Ne -> FVal
forceNe' = \case
  n@(NLocalVar x)      -> FVal (VNe n mempty)
  NSub n s             -> let ?sub = sub s ?sub in forceNe' n
  NApp t u             -> force (app (forceNe' t) (sub u ?sub))
  NPApp t l r i        -> force (lazyPapp (forceNe' t) (sub l ?sub) (sub r ?sub)
                                         (forceIVar' i))
  NProj1 t             -> force (proj1 (forceNe' t))
  NProj2 t             -> force (proj2 (forceNe' t))
  NCoe r r' x a t      -> force (lazyCoe (forceI' r) (forceI' r') x uf (force' t))
  NHCom r r' x a sys t -> force (lazyHCom (forceI' r) (forceI' r') x uf uf uf)
  NUnglue t sys        -> force (lazyUnglue t (forceSystem sys))
