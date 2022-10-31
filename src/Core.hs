
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

newtype F a = F {unF :: a}
  deriving SubAction via a

-- Syntax
--------------------------------------------------------------------------------

type Ty = Tm

data Tm
  = TopVar Lvl ~(DontShow Val)
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
  | PLam Tm Tm Name Tm          -- endpoints, body

  | Coe I I Name Ty Tm          -- coe r r' i.A t
  | HCom I I Name Ty System Tm  -- hcom r r' i.A [α → t] u

  -- we switch the field orders here compared to the papers, because
  -- this one is the sensible "dependency" order

  | GlueTy Ty System            -- Glue A [α ↦ B]      (B : Σ X (X ≃ A))
  | GlueTm Tm System            -- glue a [α ↦ b]
  | Unglue Tm System            -- unglue g [α ↦ B]

  | Nat
  | Zero
  | Suc Tm
  | NatElim Tm Tm Tm Tm         -- (P : Nat -> U) -> P z -> ((n:_) -> P n -> P (suc n)) -> (n:_) -> P n
  deriving Show

-- | Atomic equation.
data CofEq = CofEq I I
  deriving Show

-- | Conjunction of equations.
data Cof = CTrue | CAnd {-# unpack #-} CofEq Cof
  deriving Show

data System = SEmpty | SCons Cof Tm System
  deriving Show

--------------------------------------------------------------------------------

-- | We need to use this whenever we want to pass a higher-order contextual
--   argument to some combinator, like to `mapVSystem`. The problem is that
--   local implicit params are lazy. TODO: improve the strict implicit params plugin
--   to handle this case as well!
inCxt :: (IDomArg => NCofArg => DomArg => a) -> (IDomArg => NCofArg => DomArg => a)
inCxt f = let !_ = ?idom; !_ = ?cof; !_ = ?dom in f
{-# inline inCxt #-}


-- Cof and System semantics
--------------------------------------------------------------------------------

data NeCof
  = NCEq I I
  | NCAnd NeCof NeCof
  deriving Show

data VCof
  = VCTrue
  | VCFalse
  | VCNe NeCof IS.IVarSet
  deriving Show

ctrue  = F VCTrue
cfalse = F VCFalse

cand :: F VCof -> F VCof -> F VCof
cand c1 c2 = case (unF c1, unF c2) of
  (VCFalse    , c2         ) -> cfalse
  (_          , VCFalse    ) -> cfalse
  (VCTrue     , c2         ) -> F c2
  (c1         , VCTrue     ) -> F c1
  (VCNe n1 is1, VCNe n2 is2) -> F (VCNe (NCAnd n1 n2) (is1 <> is2))

iToVarSet :: I -> IS.IVarSet
iToVarSet = \case
  IVar x -> IS.singleton x
  _      -> mempty

vCofToVarSet :: F VCof -> IS.IVarSet
vCofToVarSet cof = case unF cof of
  VCTrue    -> mempty
  VCFalse   -> mempty
  VCNe _ is -> is

ceq :: F I -> F I -> F VCof
ceq c1 c2 = case (unF c1, unF c2) of
  (i, j) | i == j -> ctrue
  (i, j) -> matchIVar i
    (\x -> matchIVar j
     (\y -> F (VCNe (NCEq i j) (IS.singleton x <> IS.singleton y)))
     cfalse)
    cfalse

data NSystem cof
  = NSEmpty
  | NSCons cof ~Val (NSystem cof)
  deriving Show

data NSystem' cof = NSystem' {_nsys :: NSystem cof, _ivars :: IS.IVarSet}
  deriving Show

-- TODO: unbox
data VSystem cof
  = VSTotal ~Val
  | VSNe {-# unpack #-} (NSystem' cof)
  deriving Show

unFSystem :: F (VSystem (F VCof)) -> VSystem VCof
unFSystem = coerce

unFNSystem :: NSystem (F VCof) -> NSystem VCof
unFNSystem = coerce

unFNSystem' :: NSystem' (F VCof) -> NSystem' VCof
unFNSystem' = coerce

evalI :: SubArg => NCofArg => I -> F I
evalI i = F (doSub (sub i) ?cof)

evalEq :: SubArg => NCofArg => CofEq -> F VCof
evalEq (CofEq i j) = ceq (evalI i) (evalI j)

-- (σ : ISub Γ Δ)(α : Cof Γ) → Cof Δ → F (VCof Γ)
evalCof :: SubArg => NCofArg => Cof -> F VCof
evalCof = \case
  CTrue       -> ctrue
  CAnd eq cof -> cand (evalEq eq) (evalCof cof)

sempty :: F (VSystem (F VCof))
sempty = F (VSNe (NSystem' NSEmpty mempty))

bindI' :: (IDomArg => SubArg => NCofArg => IVar -> a)
       -> (IDomArg => SubArg => NCofArg => a)
bindI' act =
  let fresh = ?idom in
  let ?idom = ?idom + 1
      ?sub  = extSub ?sub (IVar ?idom)
      ?cof  = extSub ?cof (IVar ?idom)
  in act fresh
{-# inline bindI' #-}

bind :: (IDomArg => NCofArg => DomArg => Val -> a) -> (IDomArg => NCofArg => DomArg => a)
bind act = let v = vVar ?dom in let ?dom = ?dom + 1 in act v
{-# inline bind #-}

bindI :: (IDomArg => NCofArg => IVar -> a) -> (IDomArg => NCofArg => a)
bindI act =
  let fresh = ?idom in
  let ?idom = ?idom + 1
      ?cof  = extSub ?cof (IVar ?idom)
  in act fresh
{-# inline bindI #-}

conjIVarI :: NCof -> IVar -> I -> NCof
conjIVarI cof x i = mapSub go cof where
  go _ j = case j of
    IVar y | x == y -> i
    j               -> j

conjNeCof :: NCof -> F NeCof -> NCof
conjNeCof ncof necof = case unF necof of
  NCAnd c1 c2 -> ncof `conjNeCof` F c1 `conjNeCof` F c2
  NCEq i j -> case (i, j) of
    (IVar x, IVar y) -> let (x, i) = if x < y then (x, IVar y)
                                              else (y, IVar x) in
                        conjIVarI ncof x i
    (IVar x, j     ) -> conjIVarI ncof x j
    (i     , IVar y) -> conjIVarI ncof y i
    _                -> impossible

conjVCof :: NCof -> F VCof -> NCof
conjVCof ncof cof = case unF cof of
  VCFalse      -> impossible
  VCTrue       -> ncof
  VCNe necof _ -> conjNeCof ncof (F necof)
{-# noinline conjVCof #-}

bindCof :: F VCof -> (NCofArg => a) -> (NCofArg => a)
bindCof cof action = let ?cof = conjVCof ?cof cof in action
{-# inline bindCof #-}

scons ::
  IDomArg => NCofArg =>
  F VCof -> Val -> F (VSystem (F VCof)) -> F (VSystem (F VCof))
scons cof ~v sys = case unF sys of
  VSTotal v              -> F (VSTotal v)
  VSNe (NSystem' sys is) -> F (VSNe (NSystem' (NSCons cof v sys) (vCofToVarSet cof <> is)))
{-# inline scons #-}

evalSystem :: IDomArg => SubArg => NCofArg => DomArg => EnvArg =>
              System -> F (VSystem (F VCof))
evalSystem = \case
  SEmpty          -> sempty
  SCons cof t sys ->
    let vcof = evalCof cof in
    scons vcof (bindCof vcof (bindI \_ -> eval t)) (evalSystem sys)

-- TODO: we generally get a runtime closure from this! Try to make GHC lambda-lift function args
-- instead! Actually, CPP looks like a good candidate solution here (LOL).
mapNSystem :: (IDomArg => NCofArg => DomArg => IVar -> Val -> Val) ->
                   (IDomArg => NCofArg => DomArg => NSystem (F VCof) -> NSystem (F VCof))
mapNSystem f = go where
  go NSEmpty            = NSEmpty
  go (NSCons cof v sys) = NSCons cof (bindCof cof (bindI \i -> f i v)) (go sys)
{-# inline mapNSystem #-}

rawMapNSystem :: (Val -> Val) -> NSystem (F VCof) -> NSystem (F VCof)
rawMapNSystem f = go where
  go NSEmpty            = NSEmpty
  go (NSCons cof v sys) = NSCons cof (f v) (go sys)
{-# inline rawMapNSystem #-}

mapNSystem' :: (IDomArg => NCofArg => DomArg => IVar -> Val -> Val) ->
              (IDomArg => NCofArg => DomArg => NSystem' (F VCof) -> NSystem' (F VCof))
mapNSystem' f (NSystem' sys is) = NSystem' (mapNSystem f sys) is
{-# inline mapNSystem' #-}

mapVSystem :: (IDomArg => NCofArg => DomArg => IVar -> Val -> Val) ->
              (IDomArg => NCofArg => DomArg => F (VSystem (F VCof)) -> F (VSystem (F VCof)))
mapVSystem f sys = case unF sys of
  VSTotal v  -> F (VSTotal (bindI \i -> f i v))
  VSNe nsys  -> F (VSNe (mapNSystem' f nsys))
{-# inline mapVSystem #-}


data Ne
  = NLocalVar Lvl
  | NSub Ne Sub
  | NApp Ne Val
  | NPApp Ne ~Val ~Val I
  | NProj1 Ne
  | NProj2 Ne
  | NCoe I I Name VTy Val
  | NHCom I I Name VTy (NSystem VCof) Val
  | NUnglue Val (NSystem VCof)
  | NGlue Val (NSystem VCof)
  | NNatElim Val Val Val Ne
  deriving Show

data Env
  = ENil
  | EDef Env ~Val
  deriving Show

type EnvArg = (?env :: Env)

-- | Defunctionalized closures.
data Closure
  -- ^ Body of vanilla term evaluation.
  = CEval Sub Env Tm

  -- ^ Body of function coercions.
  | CCoePi I I Name VTy Closure Val

  -- ^ Body of function hcom.
  | CHComPi I I Name VTy Closure (NSystem VCof) Val
  deriving Show

-- | Defunctionalized closures for IVar abstraction.
data IClosure
  = ICEval Sub Env Tm
  | ICCoePathP I I Name IClosure Val Val Val
  | ICHComPathP I I Name IClosure Val Val (NSystem VCof) Val
  deriving Show

type VTy = Val

-- TODO: could we index values by forcedness? Then all canonical consructors
-- could be written without explicit F wrapping.
data Val
  = VSub Val Sub

  -- Neutrals. These are annotated with sets of blocking ivars.  Glue types are
  -- also neutral, but they're handled separately, because we have to match on
  -- them in coe/hcom.
  | VNe Ne IS.IVarSet         -- TODO: can we annotate with NCof (of the last forcing)
                              -- if stored NCof == current NCof, shortcut?
  | VGlueTy VTy (NSystem' VCof)

  -- canonicals
  | VPi Name VTy Closure
  | VLam Name Closure
  | VPathP Name IClosure Val Val
  | VPLam ~Val ~Val Name IClosure  -- annotated with endpoints
  | VSg Name VTy Closure
  | VPair Val Val
  | VU

  | VNat
  | VZero
  | VSuc Val
  deriving Show

type DomArg = (?dom :: Lvl)    -- fresh LocalVar

vVar :: Lvl -> Val
vVar x = VNe (NLocalVar x) mempty

-- Substitution
--------------------------------------------------------------------------------

instance SubAction Val where
  sub v = case v of
    VSub v s' -> VSub v (sub s')
    v         -> VSub v ?sub

instance SubAction NeCof where
  sub cof = case cof of
    NCAnd c1 c2 -> NCAnd (sub c1) (sub c2)
    NCEq i j    -> NCEq (sub i) (sub j)

instance SubAction VCof where
  sub cof = case cof of
    VCTrue        -> VCTrue
    VCFalse       -> VCFalse
    VCNe necof is -> VCNe (sub necof) (sub is)

instance SubAction (NSystem' VCof) where
  sub (NSystem' nsys is) = NSystem' (sub nsys) (sub is)

instance SubAction (NSystem VCof) where
  sub sys = case sys of
    NSEmpty          -> NSEmpty
    NSCons cof v sys -> NSCons (sub cof) (sub v) (sub sys)

instance SubAction (VSystem VCof) where
  sub sys = case sys of
    VSTotal v  -> VSTotal (sub v)
    VSNe nsys  -> VSNe (sub nsys)

instance SubAction Ne where
  sub n = case n of
    NSub n s' -> NSub n (sub s')
    n         -> NSub n ?sub

instance SubAction Closure where
  sub cl = case cl of
    CEval s' env t ->
      CEval (sub s') (sub env) t

    -- note: recursive closure sub below! TODO to scrutinize, but this is probably
    -- fine, because recursive depth is bounded by Pi type nesting.
    CCoePi r r' i a b t ->
      CCoePi (sub r) (sub r') i (sub a) (sub b) (sub t)

    CHComPi r r' i a b sys base ->
      CHComPi (sub r) (sub r') i (sub a) (sub b) (sub sys) (sub base)

instance SubAction IClosure where
  sub cl = case cl of
    ICEval s' env t ->
      ICEval (sub s') (sub env) t

    -- recursive sub here as well!
    ICCoePathP r r' i a lhs rhs p ->
      ICCoePathP (sub r) (sub r') i (sub a) (sub lhs) (sub rhs) (sub p)

    ICHComPathP r r' i a lhs rhs sys base ->
      ICHComPathP (sub r) (sub r') i (sub a) (sub lhs) (sub rhs) (sub sys) (sub base)

instance SubAction Env where
  sub e = case e of
    ENil     -> ENil
    EDef e v -> EDef (sub e) (sub v)

instance SubAction CofEq where
  sub (CofEq i j) = CofEq (sub i) (sub j)

instance SubAction Cof where
  sub cof = case cof of
    CTrue       -> CTrue
    CAnd eq cof -> CAnd (sub eq) (sub cof)

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
   unF (coe r r' i (bindI \_ -> cappf b (unF (coeFillInv r' (unF a) fu)))
                   (appf (force t) (unF (coe r' r i a fu))))

  CHComPi (forceI -> r) (forceI -> r') i a b sys base ->

    hcom r r' i (cappf b u)
         (mapVSystem                    -- TODO: fuse force $ map
            (inCxt \i t -> app (force t) u)
            (forceNSystem sys))
         (appf (force base) u)

cappf  t ~u = force  (capp t u); {-# inline cappf  #-}
cappf' t ~u = force' (capp t u); {-# inline cappf' #-}


-- | Apply an ivar closure.
icapp :: IDomArg => NCofArg => DomArg => IClosure -> I -> Val
icapp t arg = case t of
  ICEval s env t -> let ?env = env; ?sub = extSub s arg in eval t

  ICCoePathP (forceI -> r) (forceI -> r') ix a lhs rhs p ->
    let farg = forceI arg in
    com r r' ix (icappf a arg)
        ( scons (ceq farg (F I0)) lhs $
          scons (ceq farg (F I1)) rhs $
          sempty)
        (pappf (force p) lhs rhs farg)

  ICHComPathP (forceI -> r) (forceI -> r') ix a lhs rhs sys p ->

    let farg = forceI arg in

    hcom r r' ix (icappf a arg)
        ( scons (ceq farg (F I0)) lhs $
          scons (ceq farg (F I1)) rhs $
          (mapVSystem (inCxt \_ t -> papp (force t) lhs rhs farg)  -- TODO: fuse force & map
                      (forceNSystem sys))
        )
      (pappf (force p) lhs rhs farg)


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
    VPLam _ _ _ t -> icapp t (IVar x)
    VNe t is      -> VNe (NPApp t u0 u1 (IVar x)) (IS.insert x is)
    _             -> impossible
{-# inline papp #-}

pappf  ~t ~u0 ~u1 i = force  (papp t u0 u1 i); {-# inline pappf  #-}
pappf' ~t ~u0 ~u1 i = force' (papp t u0 u1 i); {-# inline pappf' #-}

-- Γ, i ⊢ coeFillⁱ r A t : A  [i=r ↦ t, i=r' ↦ coeⁱ r r' A t ]  for all r'
coeFill :: IDomArg => NCofArg => DomArg => F I -> Val -> F Val -> F Val
coeFill r a t =
  let i = ?idom - 1 in
  goCoe r (F (IVar i)) "j" (bindI \(IVar -> j) -> singleSubf (force a) i (F j)) t
{-# inline coeFill #-}

-- Γ, i ⊢ coeFillInvⁱ r' A t : A [i=r ↦ coeⁱ r' r A t, i=r' ↦ t] for all r
coeFillInv :: IDomArg => NCofArg => DomArg => F I -> Val -> F Val -> F Val
coeFillInv r' a t =
  let i = ?idom - 1 in
  goCoe r' (F (IVar i)) "j" (bindI \(IVar -> j) -> singleSubf (force a) i (F j)) t
{-# inline coeFillInv #-}

-- assumption: r /= r'
goCoe :: IDomArg => NCofArg => DomArg => F I -> F I -> Name -> F Val -> F Val -> F Val
goCoe r r' i a t = case unF a of
  VPi x a b ->
    F (VLam x (CCoePi (unF r) (unF r') i a b (unF t)))

  VSg x a b ->
    let fa    = bindI \_ -> force a
        t1    = proj1f t
        t2    = proj2f t
        bfill = bindI \_ -> cappf b (unF (coeFill r (unF fa) t1))
    in F (VPair (unF (goCoe r r' i fa t1))
                (unF (goCoe r r' i bfill t2)))

  VNat ->
    t

  VPathP j a lhs rhs ->
    F (VPLam (topSub lhs r')
             (topSub rhs r')
             j
             (ICCoePathP (unF r) (unF r') j a lhs rhs (unF t)))

  VU ->
    t

  a@(VNe n is) ->
    F (VNe (NCoe (unF r) (unF r') i a (unF t))
           (IS.insertI (unF r) $ IS.insertI (unF r') is))

  VGlueTy a sys ->
    uf

  _ ->
    impossible

coe :: IDomArg => NCofArg => DomArg => F I -> F I -> Name -> F Val -> F Val -> F Val
coe r r' i ~a t
  | unF r == unF r' = t
  | True            = goCoe r r' i a t
{-# inline coe #-}


-- | Try to project an inductive field from a system.
--   TODO: later for general ind types we will need to split systems to N copies
--   for N different constructor fields!
--   TODO: unbox this
data ProjSystem
  = Proj (NSystem (F VCof))                 -- ^ Result of projection.
  | CantProj IS.IVarSet (NSystem (F VCof))  -- ^ Return the blocking varset of the first neutral
                                                 --   component + the system which is forced up to
                                                 --   the blocking component.

zeroSys :: IDomArg => NCofArg => DomArg => NSystem (F VCof) -> ProjSystem
zeroSys = \case
  NSEmpty -> Proj NSEmpty
  NSCons cof t sys -> case zeroSys sys of
    Proj sys -> case bindCof cof (bindI \_ -> unF (force t)) of
      VZero        -> Proj (NSCons cof VZero sys)
      t@(VNe n is) -> CantProj is (NSCons cof t sys)
      _            -> impossible
    CantProj is sys -> CantProj is (NSCons cof t sys)

sucSys :: IDomArg => NCofArg => DomArg => NSystem (F VCof) -> ProjSystem
sucSys = \case
  NSEmpty -> Proj NSEmpty
  NSCons cof t sys -> case sucSys sys of
    Proj sys -> case bindCof cof (bindI \_ -> unF (force t)) of
      VSuc n       -> Proj (NSCons cof n sys)
      t@(VNe n is) -> CantProj is (NSCons cof t (rawMapNSystem VSuc sys))
      _            -> impossible
    CantProj is sys -> CantProj is (NSCons cof t sys)

-- assumption: r /= r' and system is stuch
goHComNat :: IDomArg => NCofArg => DomArg =>
             F I -> F I -> Name -> NSystem' (F VCof) -> F Val -> F Val
goHComNat r r' ix (NSystem' sys is) base = case unF base of

  VZero  -> case zeroSys sys of
              Proj _ ->
                F VZero
              CantProj is' sys' ->
                F (VNe (NHCom (unF r) (unF r') ix VNat (unFNSystem sys') VZero)
                  (is <> is'))

  VSuc n -> case sucSys sys of
              Proj sys' ->
                goHComNat r r' ix (NSystem' sys' is) (force n)
              CantProj is' sys' ->
                F (VNe (NHCom (unF r) (unF r') ix VNat (unFNSystem sys') (VSuc n))
                       (is <> is'))

  n@(VNe _ is') -> F (VNe (NHCom (unF r) (unF r') ix VNat (unFNSystem sys) n)
                     (is <> is'))

  _ -> impossible

-- assumption: r /= r' and system is stuck
goHCom :: IDomArg => NCofArg => DomArg =>
          F I -> F I -> Name -> F Val -> NSystem' (F VCof) -> F Val -> F Val
goHCom r r' ix a nsys base = case unF a of

  VPi x a b ->
    F (VLam x (CHComPi (unF r) (unF r') ix a b (unFNSystem (_nsys nsys)) (unF base)))

  VSg x a b ->

    let bfill = bindI \(IVar -> i) ->
          cappf b (unF (goHCom r (F i) ix (force a)
                               (mapNSystem' (inCxt \_ t -> proj1 (force t)) nsys)
                               (proj1f base))) in

    F (VPair
      (unF (goHCom r r' ix (force a)
                  (mapNSystem' (inCxt \_ t -> proj1 (force t)) nsys)
                  (proj1f base)))
      (unF (goCom r r' ix bfill
                  (mapNSystem' (inCxt \_ t -> proj2 (force t)) nsys)
                  (proj2f base)))
      )

  VNat -> case ?dom of
    0 -> base
    _ -> goHComNat r r' ix nsys base

  VPathP j a lhs rhs ->
    F (VPLam lhs
             rhs
             j
             (ICHComPathP (unF r) (unF r')
                          ix a lhs rhs (unFNSystem (_nsys nsys)) (unF base)))

  a@(VNe n is) ->
    F (VNe (NHCom (unF r) (unF r') ix a (unFNSystem (_nsys nsys)) (unF base))
           (IS.insertI (unF r) $ IS.insertI (unF r') (_ivars nsys <> is)))

  VU ->
    uf

  VGlueTy a sys  ->
    uf

  _ ->
    impossible

hcom :: IDomArg => NCofArg => DomArg => F I -> F I
     -> Name -> F Val -> F (VSystem (F VCof)) -> F Val -> Val
hcom r r' i ~a ~t ~b
  | unF r == unF r'          = unF b
  | VSTotal v       <- unF t = topSub v r'
  | VSNe nsys       <- unF t = unF (goHCom r r' i a nsys b)
{-# inline hcom #-}

hcomf  r r' i ~a ~t ~b = force  (hcom r r' i a t b); {-# inline hcomf  #-}
hcomf' r r' i ~a ~t ~b = force' (hcom r r' i a t b); {-# inline hcomf' #-}

-- | Identity sub except one var is mapped to
singleSubf :: IDomArg => NCofArg => DomArg => F Val -> IVar -> F I -> F Val
singleSubf t x i = forceVSub (unF t) (single x (unF i))

singleSub :: IDomArg => Val -> IVar -> F I -> Val
singleSub t x i = doSub t (single x (unF i))

-- | Instantiate the topmost var.
topSubf :: IDomArg => NCofArg => DomArg => F Val -> F I -> F Val
topSubf t i = forceVSub (unF t) (idSub ?idom `extSub` unF i)

-- | Instantiate the topmost var.
topSub :: IDomArg => Val -> F I -> Val
topSub t i = doSub t (idSub ?idom `extSub` unF i)

com :: IDomArg => NCofArg => DomArg => F I -> F I -> Name -> F Val
    -> F (VSystem (F VCof)) -> F Val -> Val
com r r' x ~a ~sys ~b =
  hcom r r' x
    (topSubf a r')
    (mapVSystem
       (inCxt \i t ->
           unF (goCoe (F (IVar i)) r' "j"
               (bindI \(IVar -> j) -> singleSubf a i (F j))
               (force t)))
       sys)
    (coe r r' x a b)
{-# inline com #-}

goCom :: IDomArg => NCofArg => DomArg => F I -> F I -> Name -> F Val
    -> NSystem' (F VCof) -> F Val -> F Val
goCom r r' x a nsys  b =
  goHCom r r' x
    (topSubf a r')
    (mapNSystem'
       (inCxt \i t ->
           unF (goCoe (F (IVar i)) r' "j"
               (bindI \(IVar -> j) -> singleSubf a i (F j))
               (force t)))
       nsys)
    (goCoe r r' x a b)

glueTy :: IDomArg => NCofArg => DomArg => Val -> F (VSystem (F VCof)) -> Val
glueTy a sys = case unF sys of
  VSTotal b -> proj1 (force b)
  VSNe nsys -> VGlueTy a (unFNSystem' nsys)
{-# inline glueTy #-}

glueTyf  ~a sys = force  (glueTy a sys); {-# inline glueTyf  #-}
glueTyf' ~a sys = force' (glueTy a sys); {-# inline glueTyf' #-}

glue :: Val -> F (VSystem (F VCof)) -> Val
glue ~t sys = case unF sys of
  VSTotal v              -> v
  VSNe (NSystem' sys is) -> VNe (NGlue t (unFNSystem sys)) is
{-# inline glue #-}

gluef  ~a sys = force  (glue a sys); {-# inline gluef  #-}
gluef' ~a sys = force' (glue a sys); {-# inline gluef' #-}

unglue :: IDomArg => NCofArg => DomArg => Val -> F (VSystem (F VCof)) -> Val
unglue t sys = case unF sys of
  VSTotal teqv           -> app (proj1f (proj2f (force teqv))) t
  VSNe (NSystem' sys is) -> VNe (NUnglue t (unFNSystem sys)) is
{-# inline unglue #-}

ungluef  ~a sys = force  (unglue a sys); {-# inline ungluef  #-}
ungluef' ~a sys = force' (unglue a sys); {-# inline ungluef' #-}

natElim :: IDomArg => NCofArg => DomArg => Val -> Val -> F Val -> F Val -> Val
natElim p z s n = case unF n of
  VZero             -> z
  VSuc (force -> n) -> s `appf` unF n `app` natElim p z s n
  VNe n is          -> VNe (NNatElim p z (unF s) n) is
  _                 -> impossible

natElimf  p z s n = force  (natElim p z s n); {-# inline natElimf  #-}
natElimf' p z s n = force' (natElim p z s n); {-# inline natElimf' #-}

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
  PLam l r x t      -> VPLam (eval l) (eval r) x (ICEval ?sub ?env t)
  Coe r r' x a t    -> unF (coe (evalI r) (evalI r') x (bindI' \_ -> evalf a) (evalf t))
  HCom r r' x a t b -> hcom (evalI r) (evalI r') x (evalf a) (evalSystem t) (evalf b)
  GlueTy a sys      -> glueTy (eval a) (evalSystem sys)
  GlueTm t sys      -> glue   (eval t) (evalSystem sys)
  Unglue t sys      -> unglue (eval t) (evalSystem sys)
  Nat               -> VNat
  Zero              -> VZero
  Suc t             -> VSuc (eval t)
  NatElim p z s n   -> natElim (eval p) (eval z) (evalf s) (evalf n)


-- Forcing
--------------------------------------------------------------------------------

forceNeCof :: NCofArg => NeCof -> F VCof
forceNeCof = \case
  NCEq i j    -> ceq (forceI i) (forceI j)
  NCAnd c1 c2 -> cand (forceNeCof c1) (forceNeCof c2)

forceCof :: NCofArg => VCof -> F VCof
forceCof = \case
  VCTrue       -> ctrue
  VCFalse      -> cfalse
  VCNe ncof is -> forceNeCof ncof

forceNeCof' :: SubArg => NCofArg => NeCof -> F VCof
forceNeCof' = \case
  NCEq i j    -> ceq (forceI' i) (forceI' j)
  NCAnd c1 c2 -> cand (forceNeCof' c1) (forceNeCof' c2)

forceCof' :: SubArg => NCofArg => VCof -> F VCof
forceCof' = \case
  VCTrue       -> ctrue
  VCFalse      -> cfalse
  VCNe ncof is -> forceNeCof' ncof

forceNSystem :: IDomArg => NCofArg => NSystem VCof -> F (VSystem (F VCof))
forceNSystem sys = let ?sub = idSub ?idom in forceNSystem' sys
{-# inline forceNSystem #-}

forceNSystem' :: IDomArg => SubArg => NCofArg => NSystem VCof -> F (VSystem (F VCof))
forceNSystem' = \case
  NSEmpty          -> sempty
  NSCons cof t sys -> scons (forceCof' cof) t (forceNSystem' sys)

forceVSub :: IDomArg => NCofArg => DomArg => Val -> Sub -> F Val
forceVSub v s = let ?sub = s in force' v
{-# inline forceVSub #-}

force :: IDomArg => NCofArg => DomArg => Val -> F Val
force = \case
  VSub v s                                 -> let ?sub = s in force' v
  VNe t is      | isUnblocked is           -> forceNe t
  VGlueTy a sys | isUnblocked (_ivars sys) -> glueTyf a (forceNSystem (_nsys sys))
  v                                        -> F v

force' :: IDomArg => SubArg => NCofArg => DomArg => Val -> F Val
force' = \case
  VSub v s                                  -> let ?sub = sub s in force' v
  VNe t is      | isUnblocked' is           -> forceNe' t
                | True                      -> F (VNe (sub t) (sub is))
  VGlueTy a sys | isUnblocked' (_ivars sys) -> glueTyf' (sub a) (forceNSystem' (_nsys sys))
                | True                      -> F (VGlueTy (sub a) (sub sys))

  VPi x a b      -> F (VPi x (sub a) (sub b))
  VLam x t       -> F (VLam x (sub t))
  VPathP x a t u -> F (VPathP x (sub a) (sub t) (sub u))
  VPLam l r x t  -> F (VPLam (sub l) (sub r) x (sub t))
  VSg x a b      -> F (VSg x (sub a) (sub b))
  VPair t u      -> F (VPair (sub t) (sub u))
  VU             -> F VU
  VNat           -> F VNat
  VZero          -> F VZero
  VSuc t         -> F (VSuc (sub t))


forceI :: NCofArg => I -> F I
forceI i = F (doSub i ?cof)

forceI' :: SubArg => NCofArg => I -> F I
forceI' i = F (sub i `doSub` ?cof)

forceIVar :: NCofArg => IVar -> F I
forceIVar x = F (lookupSub x ?cof)

forceIVar' :: SubArg => NCofArg => IVar -> F I
forceIVar' x = F (lookupSub x ?sub `doSub` ?cof)

forceNe :: IDomArg => NCofArg => DomArg => Ne -> F Val
forceNe = \case
  n@(NLocalVar x)      -> F (VNe n mempty)
  NSub n s             -> let ?sub = s in forceNe' n
  NApp t u             -> appf (forceNe t) u
  NPApp t l r i        -> pappf (forceNe t) l r (forceI i)
  NProj1 t             -> proj1f (forceNe t)
  NProj2 t             -> proj2f (forceNe t)
  NCoe r r' x a t      -> coe (forceI r) (forceI r) x (bindI \_ -> force a) (force t)
  NHCom r r' x a sys t -> hcomf (forceI r) (forceI r) x (force a)
                                 (forceNSystem sys) (force t)
  NUnglue t sys        -> ungluef t (forceNSystem sys)
  NGlue t sys          -> gluef t (forceNSystem sys)
  NNatElim p z s n     -> natElimf p z (force s) (forceNe n)

forceNe' :: IDomArg => SubArg => NCofArg => DomArg => Ne -> F Val
forceNe' = \case
  n@(NLocalVar x)      -> F (VNe n mempty)
  NSub n s             -> let ?sub = sub s in forceNe' n
  NApp t u             -> appf' (forceNe' t) (sub u)
  NPApp t l r i        -> pappf' (forceNe' t) (sub l) (sub r) (forceI' i)
  NProj1 t             -> proj1f' (forceNe' t)
  NProj2 t             -> proj2f' (forceNe' t)
  NCoe r r' x a t      -> coe (forceI' r) (forceI' r') x (bindI' \_ -> force' a) (force' t)
  NHCom r r' x a sys t -> hcomf' (forceI' r) (forceI' r') x (force' a)
                                 (forceNSystem' sys) (force' t)
  NUnglue t sys        -> ungluef' (sub t) (forceNSystem' sys)
  NGlue t sys          -> gluef' (sub t) (forceNSystem' sys)
  NNatElim p z s n     -> natElimf' (sub p) (sub z) (force' s) (forceNe' n)

-- | Eliminate head substitutions.
unSubNe :: IDomArg => Ne -> Ne
unSubNe = \case
  NSub n s -> let ?sub = s in unSubNe' n
  n        -> n

bindI'' :: (IDomArg => SubArg => a) -> (IDomArg => SubArg => a)
bindI'' act = let ?idom = ?idom + 1; ?sub = extSub ?sub (IVar ?idom) in act
{-# inline bindI'' #-}

unSubNe' :: IDomArg => SubArg => Ne -> Ne
unSubNe' = \case
  NLocalVar x          -> NLocalVar x
  NSub n s'            -> let ?sub = sub s' in unSubNe' n
  NApp t u             -> NApp (sub t) (sub u)
  NPApp p l r i        -> NPApp (sub p) (sub l) (sub r) (sub i)
  NProj1 t             -> NProj1 (sub t)
  NProj2 t             -> NProj2 (sub t)
  NCoe r r' x a t      -> NCoe (sub r) (sub r') x (bindI'' (sub a)) (sub t)
  NHCom r r' x a sys t -> NHCom (sub r) (sub r') x (sub a) (sub sys) (sub t)
  NUnglue a sys        -> NUnglue (sub a) (sub sys)
  NGlue a sys          -> NGlue (sub a) (sub sys)
  NNatElim p z s n     -> NNatElim (sub p) (sub z) (sub s) (sub n)
