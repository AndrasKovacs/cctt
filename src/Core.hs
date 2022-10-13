
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

-- coe, hcom
-}

{-

- Should we call VSystem neutral instead, and always pair it up with an ivar set?
- Better binder ergonomics in coe, hcom, mapVSystem?
- sub checks for idSub, then we don't have to write duplicate code
  where there's an extra ISub arg.

- when we make systems, should we instead use "inlined" semantic versions
  of SCons/SEmpty? (YES)

- TODO: try to get rid of typed forcing! Code should be much cleaner that way
  and overhead should be tolerable.

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

mapFVSystem' :: (IDomArg => NCofArg => DomArg => IVar -> Val -> Val)
            ->  (IDomArg => NCofArg => DomArg => FVSystem' -> FVSystem')
mapFVSystem' f = go where
  go FVSEmpty =
    FVSEmpty
  go (FVSCons cof ncof v sys) =
    FVSCons cof ncof (let ?cof = ncof in bindI \i -> f i v)
                     (go sys)
{-# inline mapFVSystem' #-}

mapFVSystem :: (IDomArg => NCofArg => DomArg => IVar -> Val -> Val) ->
               (IDomArg => NCofArg => DomArg => FVSystem -> FVSystem)
mapFVSystem f = \case
  FVSTakeBranch v      -> FVSTakeBranch (bindI \i -> f i v)
  FVSNeutral (sys, is) -> FVSNeutral (mapFVSystem' f sys, is)
{-# inline mapFVSystem #-}

-- mapVSystem :: (IDomArg => NCofArg => DomArg => IVar -> Val -> Val) ->
--               (IDomArg => NCofArg => DomArg => VSystem -> VSystem)
-- mapVSystem f = go where
--   go VSEmpty =
--     VSEmpty
--   go (FVSCons cof ncof v sys) =
--     VSCons cof ncof (let ?cof = ncof in bindI \i -> f i v)
--                     (go sys)


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
  = CEval Sub Env Tm                         -- ^ Body of vanilla term evaluation.
  | CCoePi I I Name VTy Closure Val          -- ^ Body of function coercions.
  | CHComPi I I Name VTy Closure VSystem Val  -- ^ Body of function hcom.


-- | Defunctionalized closures for IVar abstraction.
data IClosure
  = ICEval Sub Env Tm
  | ICCoePathP I I Name IClosure Val Val Val
  | ICHComPathP I I Name IClosure Val Val VSystem Val

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
  goSub v s = case v of
    VSub v s' -> VSub v (goSub s' s)
    v         -> VSub v s

instance SubAction Ne where
  goSub n s = case n of
    NSub n s' -> NSub n (goSub s' s)
    n         -> NSub n s

instance SubAction Closure where
  goSub cl s = case cl of
    CEval s' env t ->
      CEval (goSub s' s) (goSub env s) t

    -- note: recursive closure sub below! TODO to scrutinize, but this is probably
    -- fine, because recursive depth is bounded by Pi/Sigma type nesting.
    CCoePi r r' i a b t ->
      CCoePi (goSub r s) (goSub r' s) i (goSub a s) (goSub b s) (goSub t s)

    CHComPi r r' i a b sys base ->
      CHComPi (goSub r s) (goSub r' s) i (goSub a s) (goSub b s) (goSub sys s) (goSub base s)

instance SubAction IClosure where
  goSub cl s = case cl of
    ICEval s' env t ->
      ICEval (goSub s' s) (goSub env s) t

    ICCoePathP r r' i a lhs rhs p ->
      ICCoePathP (sub r s) (sub r' s) i (sub a s)
                 (sub lhs s) (sub rhs s) (sub p s)

    ICHComPathP r r' i a lhs rhs sys base ->
      ICHComPathP (sub r s) (sub r' s) i (sub a s)
                  (sub lhs s) (sub rhs s) (sub sys s) (sub base s)

instance SubAction Env where
  goSub e s = case e of
    ENil     -> ENil
    EDef e v -> EDef (goSub e s) (goSub v s)

instance SubAction CofEq where
  goSub (CofEq i j) s = CofEq (goSub i s) (goSub j s)

instance SubAction Cof where
  goSub cof s = case cof of
    CTrue       -> CTrue
    CAnd eq cof -> CAnd (goSub eq s) (goSub cof s)

instance SubAction VSystem where
  goSub sys s = case sys of
    VSEmpty          -> VSEmpty
    VSCons cof v sys -> VSCons (goSub cof s) (goSub v s) (goSub sys s)



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

  CCoePi (forceI -> r) (forceI -> r') i (force -> a) b t ->
   let fu = force u in
   unF (coe r r' i (bindI \_ -> cappf b (unF (coeFillInv r r' (unF a) fu)))
                   (appf (force t) (unF (coe r' r i a fu))))

  CHComPi (forceI -> r) (forceI -> r') i a b sys base ->
    hcom r r' i (cappf b u)
         (mapFVSystem
            (\i t -> app (force t) u)
            (forceSystem sys))
         (appf (force base) u)


cappf  t ~u = force  (capp t u); {-# inline cappf  #-}
cappf' t ~u = force' (capp t u); {-# inline cappf' #-}

-- | Apply an ivar closure.
icapp :: IDomArg => NCofArg => DomArg => IClosure -> I -> Val
icapp t arg = case t of
  ICEval s env t -> let ?env = env; ?sub = snocSub s arg in eval t

  ICCoePathP (forceI -> r) (forceI -> r') j a lhs rhs p ->
    let sys =
          VSCons (CAnd (CofEq arg I0) CTrue) lhs $
          VSCons (CAnd (CofEq arg I1) CTrue) rhs $
          VSEmpty in

    com r r' "j" (icappf a arg)
        (forceSystem sys)
        (pappf (force p) lhs rhs (forceI arg))

  ICHComPathP (forceI -> r) (forceI -> r') i a lhs rhs
              (forceSystem -> sys) base ->

    -- TODO: we need semantic FVSCons!!
    -- let sys' = VSCons _ _ $
    --            VSCons _ _ $
    --            mapFVSystem (\i t -> papp (force t) lhs rhs (forceI arg)) sys in

    -- hcom r r' i _ _ _
    uf

-- hcomⁱ r r' (Pathʲ A lhs rhs) [α ↦ t] base =
--   (λ arg. hcomⁱ r r' A [arg=0 ↦ lhs, arg=1 ↦ rhs, α ↦ t arg] (base@arg))

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

  VPathP j a lhs rhs ->
    F (VPLam j (ICCoePathP (unF r) (unF r') j a lhs rhs (unF t)))

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
goHCom r r' ix a (sys, ivarset) base = case unF a of
  VPi x a b ->
    F (VLam x (CHComPi (unF r) (unF r') ix a b (unFSystem sys) (unF base)))

  VSg x a b ->
    let proj1System :: IDomArg => NCofArg => DomArg =>
                       FVSystem' -> FVSystem'
        proj1System = mapFVSystem' (\i t -> proj1 (force t))
        {-# inline proj1System #-}

        proj2System :: IDomArg => NCofArg => DomArg =>
                       FVSystem' -> FVSystem'
        proj2System = mapFVSystem' (\i t -> proj2 (force t))
        {-# inline proj2System #-}

        bfill = bindI \i ->
          cappf b (unF (goHCom r (F (IVar i)) ix (force a)
                               (proj1System sys, ivarset)
                               (proj1f base)))
    in
    F (VPair
      (unF (goHCom r r' ix (force a)
                  (proj1System sys, ivarset)
                  (proj1f base)))
      (unF (goCom r r' ix bfill
                  (proj2System sys, ivarset)
                  (proj2f base)))
      )

  VPathP j a lhs rhs ->
    uf

-- hcomⁱ r r' (Pathʲ A lhs rhs) [α ↦ t] base =
--   (λ arg. hcomⁱ r r' A [arg=0 ↦ lhs, arg=1 ↦ rhs, α ↦ t arg] (base@arg))


  VU ->
    uf

  a@(VNe n is) ->
    F (VNe (NHCom (unF r) (unF r') ix a (unFSystem sys) (unF base))
           (IS.insertI (unF r) $ IS.insertI (unF r') (ivarset <> is)))

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
       (\i t ->
           unF (goCoe (F (IVar i)) r' "j"
               (bindI \j -> singleSubf a i (F (IVar j)))
               (force t)))
       sys)
    (coe r r' x a b)

goCom :: IDomArg => NCofArg => DomArg => F I -> F I -> Name -> F Val
    -> (FVSystem', IS.IVarSet) -> F Val -> F Val
goCom r r' x a (!sys, !sysvars) b =
  goHCom r r' x
    (singleSubf a ?idom r')
    (mapFVSystem'
       (\i t ->
           unF (goCoe (F (IVar i)) r' "j"
               (bindI \j -> singleSubf a i (F (IVar j)))
               (force t)))
       sys, sysvars)
    (goCoe r r' x a b)

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

-- (σ : ISub Γ Δ)(α : Cof Γ) → Cof Δ → FCof Γ
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

forceCof :: IDomArg => NCofArg => Cof -> FCof
forceCof cof = let ?sub = idSub ?idom in forceCof' cof

forceCof' :: SubArg => NCofArg => Cof -> FCof
forceCof' = evalCof -- for Cof, evaluation and forcing with ISub is the same

forceSystem' :: SubArg => NCofArg => VSystem -> FVSystem
forceSystem' = \case
  VSEmpty -> FVSNeutral (FVSEmpty, mempty)
  VSCons cof v sys ->
    case forceCof' cof of
      FCFalse                -> forceSystem' sys
      FCNotFalse CTrue _  is -> FVSTakeBranch v
      FCNotFalse cof ncof is -> fvsCons cof ncof is v (forceSystem' sys)

forceSystem :: IDomArg => NCofArg => VSystem -> FVSystem
forceSystem sys = let ?sub = idSub ?idom in forceSystem' sys

forceVSub :: IDomArg => NCofArg => DomArg => Val -> Sub -> F Val
forceVSub v s = let ?sub = s in force' v
{-# inline forceVSub #-}

force :: IDomArg => NCofArg => DomArg => Val -> F Val
force v = let ?sub = idSub ?idom in force' v
{-# inline force #-}

force' :: IDomArg => SubArg => NCofArg => DomArg => Val -> F Val
force' = \case
  VSub v s                           -> let ?sub = sub s ?sub in force' v
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
