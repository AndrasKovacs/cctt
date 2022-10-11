
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

data FVSystem'
  = FVSEmpty
  | FVSCons Cof NCof ~Val FVSystem'

unFSystem :: FVSystem' -> VSystem
unFSystem = \case
  FVSEmpty            -> VSEmpty
  FVSCons cof _ v sys -> VSCons cof v (unFSystem sys)

-- | An immediate result of system forcing. Marks the case where one branch is
--   true.
data FVSystem
  = FVSTakeBranch ~Val
  | FVSNeutral {-# unpack #-} (FVSystem', IS.IVarSet)

mapFVSystem' :: (Cof -> NCof -> Val -> Val) -> FVSystem' -> FVSystem'
mapFVSystem' f = go where
  go FVSEmpty                 = FVSEmpty
  go (FVSCons cof ncof v sys) = FVSCons cof ncof (f cof ncof v) (go sys)
{-# inline mapFVSystem' #-}

mapFVSystem :: NCofArg => (Cof -> NCof -> Val -> Val) -> FVSystem -> FVSystem
mapFVSystem f = \case
  FVSTakeBranch v      -> FVSTakeBranch (f CTrue ?cof v)
  FVSNeutral (sys, is) -> FVSNeutral (mapFVSystem' f sys, is)
{-# inline mapFVSystem #-}

newtype F a = F {unF :: a} deriving SubAction

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
  = CEval Sub Env Tm                 -- ^ Body of vanilla term evaluation.
  | CCoePi I I Name VTy Closure Val  -- ^ Body of function coercions.

-- | Defunctionalized closures for IVar abstraction.
data IClosure
  = ICEval Sub Env Tm

type VTy = Val

data Val
  = VSub Val Sub

  -- Neutrals. These are annotated with sets of blocking ivars.  Glue types are
  -- also neutral, but they're handled separately, because we have to match on
  -- them in coe/hcom.
  | VNe Ne IS.IVarSet               -- TODO: can we annotate with NCof (of the last forcing)
                                    -- if stored NCof == current NCof, shortcut?
  | VGlueTy VTy VSystem IS.IVarSet

  -- canonicals
  | VPi Name VTy Closure
  | VLam Name Closure
  | VPathP Name {-# unpack #-} IClosure Val Val
  | VPLam Name {-# unpack #-} IClosure
  | VSg Name VTy Closure
  | VPair Val Val
  | VU

type DomArg  = (?dom  :: Lvl)    -- fresh LocalVar

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



-- Evaluation
--------------------------------------------------------------------------------

localVar :: EnvArg => Ix -> Val
localVar x = go ?env x where
  go (EDef _ v) 0 = v
  go (EDef e _) x = go e (x - 1)
  go _          _ = impossible

-- | Apply a function. Note: *strict* in argument.
app :: IDomArg => NCofArg => DomArg => F Val -> Val -> Val
app t u = case unF t of
  VLam _ t -> capp t u
  VNe t is -> VNe (NApp t u) is
  _        -> impossible

appf  t u = force (app t u); {-# inline appf #-}
appf' t u = force' (app t u); {-# inline appf' #-}

-- | Apply a closure. Note: *lazy* in argument.
capp :: IDomArg => NCofArg => DomArg => Closure -> Val -> Val
capp t ~u = case t of

  CEval s env t ->
    let ?sub = s; ?env = EDef env u in eval t

  CCoePi (forceI -> r) (forceI -> r') i a b t
    | unF r == unF r' ->
        app (force t) u
    | True ->
        let fa = force a; fu = force u
        in unF (goCoe r r' i (bindI \_ -> cappf b (unF (coeFillInv r r' (unF fa) fu)))
                             (appf (force t) (unF (goCoe r' r i fa fu))))

cappf  t ~u = force  (capp t u); {-# inline cappf  #-}
cappf' t ~u = force' (capp t u); {-# inline cappf' #-}

-- | Apply an ivar closure.
icapp :: IDomArg => NCofArg => DomArg => IClosure -> I -> Val
icapp t i = case t of
  ICEval s env t -> let ?env = env; ?sub = snocSub s i in eval t

icappf  t i = force  (icapp t i); {-# inline icappf  #-}
icappf' t i = force' (icapp t i); {-# inline icappf' #-}

proj1 :: F Val -> Val
proj1 t = case unF t of
  VPair t _ -> t
  VNe t is  -> VNe (NProj1 t) is
  _         -> impossible

proj1f  t = force  (proj1 t); {-# inline proj1f  #-}
proj1f' t = force' (proj1 t); {-# inline proj1f' #-}

proj2 :: F Val -> Val
proj2 t = case unF t of
  VPair _ u -> u
  VNe t is  -> VNe (NProj2 t) is
  _         -> impossible

proj2f  t = force  (proj2 t); {-# inline proj2f #-}
proj2f' t = force' (proj2 t); {-# inline proj2f' #-}

-- | Apply a path.
papp :: IDomArg => NCofArg => DomArg => F Val -> Val -> Val -> F I -> Val
papp ~t ~u0 ~u1 i = case unF i of
  I0     -> u0
  I1     -> u1
  IVar x -> case unF t of
    VPLam _ t -> icapp t (IVar x)
    VNe t is  -> VNe (NPApp t u0 u1 x) (IS.insert x is)
    _         -> impossible
{-# inline papp #-}

pappf  ~t ~u0 ~u1 i = force  (papp t u0 u1 i); {-# inline pappf  #-}
pappf' ~t ~u0 ~u1 i = force' (papp t u0 u1 i); {-# inline pappf' #-}

-- Γ, i ⊢ coeFillⁱ r r' A t : A [i=r ↦ t, i=r' ↦ coeⁱ r r' A t ]
--        coeFillⁱ r r' A t := coeʲ r i (A j) t  -- fresh j

coeFill :: IDomArg => NCofArg => DomArg => F I -> F I -> Val -> F Val -> F Val
coeFill r r' a t =
  let i = ?idom - 1 in
  goCoe r (F (IVar i)) "j" (bindI \j -> forceVSub a (wk i)) t
{-# inline coeFill #-}

coeFillInv :: IDomArg => NCofArg => DomArg => F I -> F I -> Val -> F Val -> F Val
coeFillInv r r' a t =
  let i = ?idom - 1 in
  goCoe r' (F (IVar i)) "j" (bindI \j -> forceVSub a (wk i)) t
{-# inline coeFillInv #-}

-- assumption: r /= r'
goCoe :: IDomArg => NCofArg => DomArg => F I -> F I -> Name -> F Val -> F Val -> F Val
goCoe r r' i a t = case unF a of
  VPi x a b ->
    F (VLam x (CCoePi (unF r) (unF r') i a b (unF t)))

  VSg x a b ->
    let fa    = bindI \_ -> force a
        t1    = force (proj1 t)
        t2    = force (proj2 t)
        bfill = bindI \_ -> cappf b (unF (coeFill r r' (unF fa) t1))
    in F (VPair (unF (goCoe r r' i fa t1))
                (unF (goCoe r r' i bfill t2)))

  VU ->
    t

  a@(VNe n is) ->
    F (VNe (NCoe (unF r) (unF r') i a (unF t))
           (IS.insertI (unF r) $ IS.insertI (unF r') is))

  VGlueTy a sys is ->
    uf

  _ ->
    impossible

coe :: IDomArg => NCofArg => DomArg => F I -> F I -> Name -> F Val -> F Val -> F Val
coe r r' i ~a t
  | unF r == unF r' = t
  | True            = goCoe r r' i a t
{-# inline coe #-}

-- assumption: r /= r' and system is stuck
goHCom :: IDomArg => NCofArg => DomArg =>
          F I -> F I -> Name -> F Val -> (FVSystem', IS.IVarSet) -> F Val -> F Val
goHCom r r' x a sys b = case unF a of
  VPi x a b ->
    uf

  VSg x a b ->
    uf

  VU ->
    uf

  a@(VNe n is) ->
    F (VNe (NHCom (unF r) (unF r') x a (unFSystem (fst sys)) (unF b))
           (IS.insertI (unF r) $ IS.insertI (unF r') (snd sys <> is)))

  VGlueTy a sys is ->
    uf

  _ ->
    impossible

hcom :: IDomArg => NCofArg => DomArg => F I -> F I
     -> Name -> F Val -> FVSystem -> F Val -> Val
hcom r r' i ~a ~t ~b
  | unF r == unF r'      = unF b
  | FVSTakeBranch v <- t = singleSub v ?idom r'
  | FVSNeutral sys  <- t = unF (goHCom r r' i a sys b)
{-# inline hcom #-}

hcomf  r r' i ~a ~t ~b = force  (hcom r r' i a t b); {-# inline hcomf  #-}
hcomf' r r' i ~a ~t ~b = force' (hcom r r' i a t b); {-# inline hcomf' #-}

inst :: IDomArg => NCofArg => DomArg => Val -> F I -> F Val
inst v i = forceVSub v (snocSub (idSub ?idom) (unF i))
{-# inline inst #-}

singleSubf :: IDomArg => NCofArg => DomArg => F Val -> IVar -> F I -> F Val
singleSubf t x i = forceVSub (unF t) (single x (unF i))

singleSub :: IDomArg => Val -> IVar -> F I -> Val
singleSub t x i = sub t (single x (unF i))

com :: IDomArg => NCofArg => DomArg => F I -> F I -> Name -> F Val
    -> FVSystem -> F Val -> Val
com r r' x ~a ~sys ~b =
  hcom r r' x
    (singleSubf a ?idom r')
    (mapFVSystem
       (\cof ncof t ->
           let ?cof = ncof in
           bindI \i ->
           unF (goCoe (F (IVar i)) r' "j"
                 (bindI \j -> singleSubf a i (F (IVar j)))
                 (force t)))
       sys)
    (coe r r' x a b)

  -- comⁱ r r' A [α ↦ t] b :=
  --   hcomⁱ r r' (A r') [α ↦ coeʲ i r' (A j) t] (coeⁱ r r' A b)  -- fresh j

evalI :: SubArg => NCofArg => I -> F I
evalI i = forceI (sub i ?sub)

evalIVar :: SubArg => NCofArg => IVar -> F I
evalIVar x = forceI (lookupSub x ?sub)

-- Evaluation for cof & systems
------------------------------------------------------------

data FCof = FCFalse | FCNotFalse Cof NCof IS.IVarSet

iToVarSet :: I -> IS.IVarSet
iToVarSet = \case
  IVar x -> IS.singleton x
  _      -> mempty

cofEqVars :: CofEq -> IS.IVarSet
cofEqVars (CofEq i j) = iToVarSet i <> iToVarSet j

cofVars :: Cof -> IS.IVarSet
cofVars cof = go mempty cof where
  go acc = \case
    CTrue       -> acc
    CAnd eq cof -> go (acc <> cofEqVars eq) cof

conjFCof :: CofEq -> FCof -> FCof
conjFCof eq = \case
  FCNotFalse cof ncof is -> FCNotFalse (CAnd eq cof) ncof (cofVars cof <> is)
  FCFalse                -> FCFalse

updNCof :: NCof -> IVar -> I -> NCof
updNCof cof x i = mapSub go cof where
  go _ j = case j of
    IVar y | x == y -> i
    j               -> j

evalCof :: SubArg => NCofArg => Cof -> FCof
evalCof = \case
  CTrue -> FCNotFalse CTrue ?cof mempty
  CAnd (CofEq i j) alpha -> case (unF (evalI i), unF (evalI j)) of
    (i, j) | i == j  -> evalCof alpha
    (IVar x, IVar y) -> let (x, i) = if x < y then (x, IVar y)
                                              else (y, IVar x) in
                        let ?cof = updNCof ?cof x i in
                        conjFCof (CofEq (IVar x) i) (evalCof alpha)
    (IVar x, j     ) -> let ?cof = updNCof ?cof x j in
                        conjFCof (CofEq (IVar x) j) (evalCof alpha)
    (i     , IVar y) -> let ?cof = updNCof ?cof y i in
                        conjFCof (CofEq (IVar y) i) (evalCof alpha)
    _                -> FCFalse

fvsCons :: Cof -> NCof -> IS.IVarSet -> Val -> FVSystem -> FVSystem
fvsCons cof ncof is ~v = \case
  FVSNeutral (sys, is') -> FVSNeutral (FVSCons cof ncof v sys, is <> is')
  FVSTakeBranch v'      -> FVSTakeBranch v'

evalSystem :: IDomArg => SubArg => NCofArg => DomArg => EnvArg =>
              System -> FVSystem
evalSystem = \case
  SEmpty -> FVSNeutral (FVSEmpty, mempty)
  SCons cof t sys ->
    case evalCof cof of
      FCFalse                -> evalSystem sys
      FCNotFalse CTrue _  is -> FVSTakeBranch (eval t)
      FCNotFalse cof ncof is -> fvsCons cof ncof is (let ?cof = ncof in eval t)
                                                    (evalSystem sys)


------------------------------------------------------------

glueTy :: Val -> FVSystem -> Val
glueTy ~a sys = uf
{-# inline glueTy #-}

glueTyf  ~a sys = force  (glueTy a sys); {-# inline glueTyf  #-}
glueTyf' ~a sys = force' (glueTy a sys); {-# inline glueTyf' #-}

glueTm :: Val -> FVSystem -> Val
glueTm = uf
{-# inline glueTm #-}

unglue :: Val -> FVSystem -> Val
unglue ~a sys = uf
{-# inline unglue #-}

ungluef  ~a sys = force  (unglue a sys); {-# inline ungluef  #-}
ungluef' ~a sys = force' (unglue a sys); {-# inline ungluef' #-}

bindI' :: (IDomArg => SubArg => NCofArg => IVar -> a)
       -> (IDomArg => SubArg => NCofArg => a)
bindI' act =
  let fresh = ?idom in
  let ?idom = ?idom + 1
      ?sub  = snocSub ?sub (IVar ?idom)
      ?cof  = snocSub ?cof (IVar ?idom)
  in act fresh
{-# inline bindI' #-}

bindI :: (IDomArg => NCofArg => IVar -> a) -> (IDomArg => NCofArg => a)
bindI act =
  let fresh = ?idom in
  let ?idom = ?idom + 1
      ?cof  = snocSub ?cof (IVar ?idom)
  in act fresh
{-# inline bindI #-}

-- conj :: NCof -> Cof -> NCof
-- conj ncof = \case
--   CTrue -> ncof
--   CAnd (CofEq i j) alpha -> case (sub i ncof, sub j ncof) of
--     (IVar x, IVar y) -> _

-- bindCof :: Cof -> (NCofArg => a) -> (NCofArg => a)
-- bindCof alpha act =
--   let ?cof = conj ?cof alpha in act

evalf :: IDomArg => SubArg => NCofArg => DomArg => EnvArg => Tm -> F Val
evalf t = force (eval t)
{-# inline evalf #-}

eval :: IDomArg => SubArg => NCofArg => DomArg => EnvArg => Tm -> Val
eval = \case
  TopVar _ v        -> coerce v
  LocalVar x        -> localVar x
  Let x _ t u       -> let ~v = eval t in let ?env = EDef ?env v in eval u
  Pi x a b          -> VPi x (eval a) (CEval ?sub ?env b)
  App t u           -> app (evalf t) (eval u)
  Lam x t           -> VLam x (CEval ?sub ?env t)
  Sg x a b          -> VSg x (eval a) (CEval ?sub ?env b)
  Pair t u          -> VPair (eval t) (eval u)
  Proj1 t           -> proj1 (evalf t)
  Proj2 t           -> proj2 (evalf t)
  U                 -> VU
  PathP x a t u     -> VPathP x (ICEval ?sub ?env a) (eval t) (eval u)
  PApp t u0 u1 i    -> papp (evalf t) (eval u0) (eval u1) (evalI i)
  PLam x t          -> VPLam x (ICEval ?sub ?env t)
  Coe r r' x a t    -> unF (coe (evalI r) (evalI r') x (bindI' \_ -> evalf a) (evalf t))
  HCom r r' x a t b -> hcom (evalI r) (evalI r') x (evalf a) (evalSystem t) (evalf b)
  GlueTy a sys      -> glueTy (eval a) (evalSystem sys)
  GlueTm t sys      -> glueTm (eval t) (evalSystem sys)
  Unglue t sys      -> unglue (eval t) (evalSystem sys)



-- Forcing
--------------------------------------------------------------------------------

forceSystem :: IDomArg => NCofArg => DomArg => VSystem -> FVSystem
forceSystem = uf

forceSystem' :: IDomArg => SubArg => NCofArg => DomArg => VSystem -> FVSystem
forceSystem' = uf

forceVSub :: IDomArg => NCofArg => DomArg => Val -> Sub -> F Val
forceVSub v s = let ?sub = s in force' v
{-# inline forceVSub #-}

force :: IDomArg => NCofArg => DomArg => Val -> F Val
force = \case
  VSub v s                          -> forceVSub v s
  VNe t is         | isUnblocked is -> forceNe t
  VGlueTy a sys is | isUnblocked is -> glueTyf a (forceSystem sys)
  v                                 -> F v

force' :: IDomArg => SubArg => NCofArg => DomArg => Val -> F Val
force' = \case
  VSub v s                           -> impossible
  VNe t is         | isUnblocked' is -> forceNe' t
  VGlueTy a sys is | isUnblocked' is -> glueTyf' a (forceSystem' sys)
  v                                  -> F (sub v ?sub)

forceI :: NCofArg => I -> F I
forceI i = F (sub i ?cof)

forceI' :: SubArg => NCofArg => I -> F I
forceI' i = F (i `sub` ?sub `sub` ?cof)

forceIVar :: NCofArg => IVar -> F I
forceIVar x = F (lookupSub x ?cof)

forceIVar' :: SubArg => NCofArg => IVar -> F I
forceIVar' x = F (lookupSub x ?sub `sub` ?cof)

forceNSub :: IDomArg => NCofArg => DomArg => Ne -> Sub -> F Val
forceNSub n s = let ?sub = s in forceNe' n
{-# inline forceNSub #-}

forceNe :: IDomArg => NCofArg => DomArg => Ne -> F Val
forceNe = \case
  n@(NLocalVar x)      -> F (VNe n mempty)
  NSub n s             -> forceNSub n s
  NApp t u             -> appf (forceNe t) u
  NPApp t l r i        -> pappf (forceNe t) l r (forceIVar i)
  NProj1 t             -> proj1f (forceNe t)
  NProj2 t             -> proj2f (forceNe t)
  NCoe r r' x a t      -> coe (forceI r) (forceI r') x (bindI \_ -> force a) (force t)
  NHCom r r' x a sys t -> hcomf (forceI r) (forceI r') x uf uf uf
  NUnglue t sys        -> ungluef t (forceSystem sys)

forceNe' :: IDomArg => SubArg => NCofArg => DomArg => Ne -> F Val
forceNe' = \case
  n@(NLocalVar x)      -> F (VNe n mempty)
  NSub n s             -> let ?sub = sub s ?sub in forceNe' n
  NApp t u             -> appf' (forceNe' t) (sub u ?sub)
  NPApp t l r i        -> pappf' (forceNe' t) (sub l ?sub) (sub r ?sub) (forceIVar' i)
  NProj1 t             -> proj1f' (forceNe' t)
  NProj2 t             -> proj2f' (forceNe' t)
  NCoe r r' x a t      -> coe (forceI' r) (forceI' r') x (bindI' \_ -> force' a) (force' t)
  NHCom r r' x a sys t -> hcomf' (forceI' r) (forceI' r') x (force' a)
                                 (forceSystem' sys) (force' t)
  NUnglue t sys        -> ungluef' t (forceSystem' sys)
