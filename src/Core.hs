
module Core where

import Common
import CoreTypes
import Cubical

import Statistics (bumpHCom, bumpHCom')

----------------------------------------------------------------------------------------------------
{-
TODO:
- purge stability annotations
  - problem: we need some way to actually terminate in forcing
    It was rather delicate that the previous varset forcing terminated. We
    relied on:
      - A freshly forced value always has an annotation which immediately block more
        forcing.

    This was true because forcing applied the action of the current cof to all critical
    ivars. After forcing, the action of the same cof becomes identity on the ivar set.

    If we have connections, there is no action of cofs that could be applied, and it seems
    that it does not work anymore to remember sets of ivars.

  - solution 1:
    - Every semantic function that's involved in frc returns an extra flag as output,
      which indicates whether the call "progressed" or "blocked".
    - A helper function for all of these which immediately discards the flag.

- ensure that closed eval does not need to go under cofs
  - problem:
    - closed hcomind applies a projection under a cof, which
      means that eval does need to happen under there
  - solution:
    defunctionalize hcom components as well

- implement connections
- add hcomU

Not priority
- have neutral type annotation instead of path annotation only?
  (not super important if we don't want unit eta)
- have native fixpoints + case trees, drop top-level recursion

-}

type EvalArgs a = SubArg => NCofArg => DomArg => EnvArg => RecurseArg => a

----------------------------------------------------------------------------------------------------
-- Context manipulation primitives
----------------------------------------------------------------------------------------------------

-- | Get a fresh ivar when not working under a Sub.
freshIVar :: (NCofArg => IVar -> a) -> (NCofArg => a)
freshIVar act =
  let fresh = dom ?cof in
  let ?cof  = lift ?cof in
  seq ?cof (act fresh)
{-# inline freshIVar #-}

freshI :: (NCofArg => I -> a) -> (NCofArg => a)
freshI act = freshIVar \i -> act (IVar i)
{-# inline freshI #-}

-- | Get a fresh ivar, when working under a Sub.
freshIVarS :: (SubArg => NCofArg => IVar -> a) -> (SubArg => NCofArg => a)
freshIVarS act =
  let fresh = dom ?cof in
  let ?sub  = lift ?sub in
  let ?cof  = lift ?cof in
  seq ?sub (seq ?cof (act fresh))
{-# inline freshIVarS #-}

-- | Push multiple fresh ivars.
freshIVarsS :: [Name] -> (SubArg => NCofArg => a) -> (SubArg => NCofArg => a)
freshIVarsS is act = case is of
  []   -> act
  _:is -> freshIVarS \_ -> freshIVarsS is act
{-# inline freshIVarsS #-}

-- | Define the next fresh ivar to an expression.
defineI :: I -> (SubArg => a) -> (SubArg => a)
defineI i act = let ?sub = ?sub `ext` i in seq ?sub act
{-# inline defineI #-}

-- | Get a fresh fibrant var.
fresh :: (DomArg => Val -> a) -> (DomArg => a)
fresh act = let v = vVar ?dom in let ?dom = ?dom + 1 in seq ?dom (act v)
{-# inline fresh #-}

-- | Define the next fresh fibrant var to a value.
define :: Val -> (EnvArg => a) -> (EnvArg => a)
define ~v act = let ?env = EDef ?env v in act
{-# inline define #-}

wkIS :: (SubArg => NCofArg => a) -> (SubArg => NCofArg => a)
wkIS act = let ?sub = setCod (cod ?sub - 1) ?sub in seq ?sub act
{-# inline wkIS #-}

assumeCof :: NeCof -> (NCofArg => a) -> (NCofArg => a)
assumeCof cof act = let ?cof = conjNeCof cof in seq ?cof act
{-# inline assumeCof #-}

----------------------------------------------------------------------------------------------------
-- Creating semantic binders
----------------------------------------------------------------------------------------------------

bindCof :: NeCof' -> (NCofArg => a) -> (NCofArg => BindCof a)
bindCof (NeCof' cof c) act = let ?cof = cof in BindCof c act
{-# inline bindCof #-}

bindCofLazy :: NeCof' -> (NCofArg => a) -> (NCofArg => BindCofLazy a)
bindCofLazy (NeCof' cof c) act = let ?cof = cof in BindCofLazy c act
{-# inline bindCofLazy #-}

bindI :: Name -> (NCofArg => I -> a) -> (NCofArg => BindI a)
bindI x act = freshIVar \i -> BindI x i (act (IVar i))
{-# inline bindI #-}

bindIVar :: Name -> (NCofArg => IVar -> a) -> (NCofArg => BindI a)
bindIVar x act = freshIVar \i -> BindI x i (act i)
{-# inline bindIVar #-}

bindILazy :: Name -> (NCofArg => I -> a) -> (NCofArg => BindILazy a)
bindILazy x act = freshIVar \i -> BindILazy x i (act (IVar i))
{-# inline bindILazy #-}

bindIS :: Name -> (SubArg => NCofArg => I -> a) -> (SubArg => NCofArg => BindI a)
bindIS x act = freshIVarS \i -> BindI x i (act (IVar i))
{-# inline bindIS #-}

bindILazyS :: Name -> (SubArg => NCofArg => I -> a) -> (SubArg => NCofArg => BindILazy a)
bindILazyS x act = freshIVarS \i -> BindILazy x i (act (IVar i))
{-# inline bindILazyS #-}


-- Systems
----------------------------------------------------------------------------------------------------

vsempty :: VSys
vsempty = VSNe NSEmpty

vscons :: NCofArg => VCof -> (NCofArg => Val) -> VSys -> VSys
vscons cof v ~sys = case cof of
  VCTrue   -> VSTotal v
  VCFalse  -> sys
  VCNe cof -> case sys of
    VSTotal v' -> VSTotal v'
    VSNe sys   -> VSNe (NSCons (bindCofLazy cof v) sys)
{-# inline vscons #-}

-- | Extend a *neutral* system with a *non-true* cof.
nscons :: NCofArg => VCof -> (NCofArg => Val) -> NeSys -> NeSys
nscons cof v ~sys = case cof of
  VCTrue   -> impossible
  VCFalse  -> sys
  VCNe cof -> NSCons (bindCofLazy cof v) sys
{-# inline nscons #-}

evalSys :: EvalArgs (Sys -> VSys)
evalSys = \case
  SEmpty          -> vsempty
  SCons cof t sys -> vscons (evalCof cof) (eval t) (evalSys sys)

vshempty :: VSysHCom
vshempty = VSHNe NSHEmpty

vshcons :: NCofArg => VCof -> Name -> (NCofArg => I -> Val) -> VSysHCom -> VSysHCom
vshcons cof i v ~sys = case cof of
  VCTrue   -> VSHTotal (bindILazy i v)
  VCFalse  -> sys
  VCNe cof -> case sys of
    VSHTotal v' -> VSHTotal v'
    VSHNe sys   -> VSHNe (NSHCons (bindCof cof (bindILazy i v)) sys)
{-# inline vshcons #-}

vshconsS :: SubArg => NCofArg => VCof -> Name -> (SubArg => NCofArg => I -> Val) -> VSysHCom -> VSysHCom
vshconsS cof i v ~sys = case cof of
  VCTrue   -> VSHTotal (bindILazyS i v)
  VCFalse  -> sys
  VCNe cof -> case sys of
    VSHTotal v' -> VSHTotal v'
    VSHNe sys   -> VSHNe (NSHCons (bindCof cof (bindILazyS i v)) sys)
{-# inline vshconsS #-}

evalSysHCom :: EvalArgs (SysHCom -> VSysHCom)
evalSysHCom = \case
  SHEmpty            -> vshempty
  SHCons cof x t sys -> vshconsS (evalCof cof) x (\_ -> eval t) (evalSysHCom sys)

occursInNeCof :: NeCof -> IVar -> Bool
occursInNeCof cof i' = case cof of
  NCEq i j -> i == IVar i' || j == IVar i'

-- Alternative hcom and com semantics which shortcuts to term instantiation if
-- the system is total. We make use of the knowledge that the system argument
-- comes from the syntax.
----------------------------------------------------------------------------------------------------

data VSysHComSC = VSHTotalSC Name Tm | VSHNeSC NeSysHCom deriving Show

vshemptySC :: VSysHComSC
vshemptySC = VSHNeSC NSHEmpty

vshconsSSC :: EvalArgs (VCof -> Name -> Tm -> VSysHComSC -> VSysHComSC)
vshconsSSC cof i t ~sys = case cof of
  VCTrue   -> VSHTotalSC i t
  VCFalse  -> sys
  VCNe cof -> case sys of
    VSHTotalSC x t -> VSHTotalSC x t
    VSHNeSC sys    -> VSHNeSC (NSHCons (bindCof cof (bindILazyS i \_ -> eval t)) sys)
{-# inline vshconsSSC #-}

evalSysHComSC :: EvalArgs (SysHCom -> VSysHComSC)
evalSysHComSC = \case
  SHEmpty            -> vshemptySC
  SHCons cof x t sys -> vshconsSSC (evalCof cof) x t (evalSysHComSC sys)

hcomSC :: EvalArgs (I -> I -> Val -> VSysHComSC -> Val -> Val)
hcomSC r r' ~a ~t ~b
  | r == r'             = b
  | VSHTotalSC x t <- t = let ?sub = ?sub `ext` r' in eval t
  | VSHNeSC nsys   <- t = hcomdn r r' a nsys b
{-# inline hcomSC #-}

comSC :: EvalArgs (I -> I -> BindI Val -> VSysHComSC -> Val -> Val)
comSC r r' ~a ~sys ~b
  | r == r'               = b
  | VSHTotalSC x t <- sys = let ?sub = ?sub `ext` r' in eval t
  | VSHNeSC nsys   <- sys = hcomdn r r' (a ∙ r')
                              (mapNeSysHCom (\i t -> coe i r' a (t ∙ i)) nsys)
                              (coed r r' a b)
{-# inline comSC #-}

----------------------------------------------------------------------------------------------------
-- Mapping
----------------------------------------------------------------------------------------------------

unBindCof :: NCofArg => BindCof a -> NeCof'
unBindCof t = NeCof' (conjNeCof (t^.binds)) (t^.binds)
{-# inline unBindCof #-}

unBindCofLazy :: NCofArg => BindCofLazy a -> NeCof'
unBindCofLazy t = NeCof' (conjNeCof (t^.binds)) (t^.binds)
{-# inline unBindCofLazy #-}

mapBindCof :: NCofArg => BindCof a -> (NCofArg => a -> b) -> BindCof b
mapBindCof t f = bindCof (unBindCof t) (f (t^.body))
{-# inline mapBindCof #-}

mapBindCofLazy :: NCofArg => BindCofLazy a -> (NCofArg => a -> b) -> BindCofLazy b
mapBindCofLazy t f = bindCofLazy (unBindCofLazy t) (f (t^.body))
{-# inline mapBindCofLazy #-}

bindIFromLazy :: BindILazy a -> BindI a
bindIFromLazy (BindILazy x i a) = BindI x i a
{-# inline bindIFromLazy #-}

mapBindI :: SubAction a => NCofArg => BindI a -> (NCofArg => I -> a -> b) -> BindI b
mapBindI t f = bindI (t^.name) (\i -> f i (t ∙ i))
{-# inline mapBindI #-}

mapBindILazy :: SubAction a => NCofArg => BindILazy a -> (NCofArg => I -> a -> b) -> BindILazy b
mapBindILazy t f = bindILazy (t^.name) (\i -> f i (t ∙ i))
{-# inline mapBindILazy #-}

mapBindIVar :: SubAction a => NCofArg => BindI a -> (NCofArg => IVar -> a -> b) -> BindI b
mapBindIVar t f = bindIVar (t^.name) (\i -> f i (t ∙ IVar i))
{-# inline mapBindIVar #-}

-- | Map over a binder in a way which *doesn't* rename the bound variable to a
--   fresh one.  In this case, the mapping function cannot refer to values in
--   external scope, it can only depend on the value under the binder. This can
--   be useful when we only do projections under a binder. The case switch in
--   `coed` on the type argument is similar.
umapBindILazy :: NCofArg => BindILazy a -> (NCofArg => I -> a -> b) -> BindILazy b
umapBindILazy (BindILazy x i a) f =
  let ?cof = lift (setDom i ?cof) in
  seq ?cof (BindILazy x i (f (IVar i) a))
{-# inline umapBindILazy #-}

umapBindI :: NCofArg => BindI a -> (NCofArg => I -> a -> b) -> BindI b
umapBindI (BindI x i a) f =
  let ?cof = lift (setDom i ?cof) in
  seq ?cof (BindI x i (f (IVar i) a))
{-# inline umapBindI #-}

proj1BindIFromLazy :: NCofArg => DomArg => Name -> BindILazy Val -> BindI Val
proj1BindIFromLazy x t = umapBindI (bindIFromLazy t) (\_ -> proj1 x)
{-# inline proj1BindIFromLazy #-}

mapNeSys :: NCofArg => (NCofArg => Val -> Val) -> NeSys -> NeSys
mapNeSys f sys = go sys where
  go = \case
    NSEmpty      -> NSEmpty
    NSCons t sys -> NSCons (mapBindCofLazy t f) (go sys)
{-# inline mapNeSys #-}

mapNeSysHCom :: NCofArg => (NCofArg => I -> BindILazy Val -> Val) -> NeSysHCom -> NeSysHCom
mapNeSysHCom f sys = go sys where
  go = \case
    NSHEmpty      -> NSHEmpty
    NSHCons t sys -> NSHCons (mapBindCof t \t -> bindILazy (t^.name) (\i -> f i t)) (go sys)
{-# inline mapNeSysHCom #-}

mapVSysHCom :: NCofArg => (NCofArg => I -> BindILazy Val -> Val) -> VSysHCom -> VSysHCom
mapVSysHCom f sys = case sys of
  VSHTotal v -> VSHTotal (bindILazy (v^.name) \i -> f i v)
  VSHNe sys  -> VSHNe (mapNeSysHCom f sys)
{-# inline mapVSysHCom #-}

mapNeSysToH :: NCofArg => (NCofArg => I -> Val -> Val) -> NeSys -> NeSysHCom
mapNeSysToH f sys = case sys of
  NSEmpty      -> NSHEmpty
  NSCons t sys -> NSHCons (bindCof (unBindCofLazy t) (bindILazy i_ \i -> f i (t^.body)))
                          (mapNeSysToH f sys)
{-# inline mapNeSysToH #-}

mapNeSysFromH :: NCofArg => (NCofArg => BindILazy Val -> Val) -> NeSysHCom -> NeSys
mapNeSysFromH f sys = case sys of
  NSHEmpty      -> NSEmpty
  NSHCons t sys -> NSCons (bindCofLazy (unBindCof t) (f (t^.body))) (mapNeSysFromH f sys)
{-# inline mapNeSysFromH #-}

-- | Filter out the components of system which depend on a binder, and at the same time
--   push the binder inside so that we get a NeSysHCom'.
forallNeSys :: BindI NeSys -> NeSysHCom
forallNeSys (BindI x i sys) = case sys of
  NSEmpty -> NSHEmpty
  NSCons t sys ->
    if occursInNeCof (t^.binds) i
      then forallNeSys (BindI x i sys)
      else case forallNeSys (BindI x i sys) of
        sys -> NSHCons (BindCof (t^.binds) (BindILazy x i (t^.body))) sys

-- System concatenation
----------------------------------------------------------------------------------------------------

catNeSysHCom :: NeSysHCom -> NeSysHCom -> NeSysHCom
catNeSysHCom sys sys' = case sys of
  NSHEmpty      -> sys'
  NSHCons t sys -> NSHCons t (catNeSysHCom sys sys')

----------------------------------------------------------------------------------------------------
-- Overloaded application and forcing
----------------------------------------------------------------------------------------------------

infixl 8 ∙
class Apply a b c a1 a2 | a -> b c a1 a2 where
  (∙) :: a1 => a2 => a -> b -> c

instance Apply NamedClosure Val Val NCofArg DomArg where
  (∙) = capp; {-# inline (∙) #-}

app' :: NCofArg => DomArg => Val -> Val -> Res
app' t u = case frc t of
  VLam t             -> progress (t ∙ u)
  VNe t              -> block $ VNe (NApp t u)
  v@VHole{}          -> block $ v
  VUnf inf v v'      -> block $ VUnf inf (FApp v u) (v' ∙ u)
  _                  -> impossible

instance Apply Val Val Val NCofArg DomArg where
  (∙) t u = (app' t u)^.val
  {-# inline (∙) #-}

instance Apply (BindI a) I a (SubAction a) NCofArg where
  (∙) (BindI x i a) j
    | IVar i == j = a
    | otherwise   = appSub (wkSub (idSub i) `ext` j) a
  {-# inline (∙) #-}

instance Apply (BindILazy a) I a (SubAction a) NCofArg where
  (∙) (BindILazy x i a) j
    | IVar i == j = a
    | otherwise   = appSub (wkSub (idSub i) `ext` j) a
  {-# inline (∙) #-}

instance Apply NamedIClosure I Val NCofArg DomArg where
  (∙) = icapp; {-# inline (∙) #-}

infixl 8 ∙~
(∙~) :: NCofArg => DomArg => Val -> Val -> Val
(∙~) t ~u = case frc t of
  VLam t      -> t ∙ u
  VNe t       -> VNe (NApp t u)
  v@VHole{}   -> v
  VUnf x v v' -> VUnf x (FApp v u) (v' ∙ u)
  _           -> impossible
{-# inline (∙~) #-}

----------------------------------------------------------------------------------------------------
-- Evaluation
----------------------------------------------------------------------------------------------------

localVar :: EnvArg => Ix -> Val
localVar x = go ?env x where
  go (EDef _ v) 0 = v
  go (EDef e _) x = go e (x - 1)
  go _          _ = impossible

-- | Apply a closure. Note: *lazy* in argument.
capp :: NCofArg => DomArg => NamedClosure -> Val -> Val
capp (NCl _ t) ~u = case t of

  CEval (EC s env rc t) ->
    let ?env = EDef env u; ?sub = wkSub s; ?recurse = rc in eval t

  CEvalLazy (ECL s env rc t) ->
    let ?env = EDef env u; ?sub = wkSub s; ?recurse = rc in eval t

  CSplit b ecs  -> case_ u b ecs
  CHSplit b ecs -> hcase u b ecs

  CCoePi r r' a b t ->
    let ~x = u in
    coe r r' (bindI j_ \j -> b ∙ j ∙ coe r' j a x) (t ∙ coe r' r a x)

  CHComPi r r' a b sys base ->
    hcom r r'
      (b ∙ u)
      (mapVSysHCom (\i t -> t ∙ i ∙ u) (frc sys))
      (base ∙ u)

  CConst v -> v

  -- isEquiv : (A → B) → U
  -- isEquiv A B f :=
  --     (g^1    : B → A)
  --   × (linv^2 : (x^4 : A) → Path A (g (f x)) x)
  --   × (rinv^3 : (x^5 : B) → Path B (f (g x)) x)
  --   × (coh    : (x^6 : A) →
  --             PathP (i^7) (Path B (f (linv x {x}{g (f x)} i)) (f x))
  --                   (refl B (f x))
  --                   (rinv (f x)))

  CIsEquiv1 a b f -> let ~g = u in
    VSg (VPi a $ NCl x_ $ CIsEquiv4 a f g) $ NCl linv_ $ CIsEquiv2 a b f g

  CIsEquiv2 a b f g -> let ~linv = u in
    VSg (VPi b $ NCl x_ $ CIsEquiv5 b f g) $ NCl rinv_ $ CIsEquiv3 a b f g linv

  CIsEquiv3 a b f g linv -> let ~rinv = u in
    VWrap coh_ (VPi a $ NCl a_ $ CIsEquiv6 b f g linv rinv)

  CIsEquiv4 a f g -> let ~x = u in path a (g ∙ (f ∙ x)) x
  CIsEquiv5 b f g -> let ~x = u in path b (f ∙ (g ∙ x)) x

  CIsEquiv6 b f g linv rinv ->
    let ~x  = u
        ~fx = f ∙ x in
    VPath (NICl i_ $ ICIsEquiv7 b f g linv x) (rinv ∙ fx) (refl fx)

  -- equiv A B = (f* : A -> B) × isEquiv a b f
  CEquiv a b -> let ~f = u in isEquiv a b f

  -- [A]  (B* : U) × equiv B A
  CEquivInto a -> let ~b = u in equiv b a

  -- ------------------------------------------------------------

  C'λ'a''a     -> u
  C'λ'a'i''a   -> refl u
  C'λ'a'i'j''a -> let ru = refl u in VPLam ru ru $ NICl i_ $ ICConst ru

{-
  coeIsEquiv : (A : I → U) (r r' : I) → isEquiv (λ x. coe r r' A x)
  coeIsEquiv A r r' =

    ffill i x      := coe r i A x
    gfill i x      := coe i r A x
    linvfill i x j := hcom r i (A r) [j=0 k. coe k r A (coe r k A x); j=1 k. x] x
    rinvfill i x j := hcom i r (A i) [j=0 k. coe k i A (coe i k A x); j=1 k. x] x

    g    := λ x^0. gfill r' x
    linv := λ x^0 j^1. linvfill r' x j
    rinv := λ x^0 j^1. rinvfill r' x j
    coh  := λ x^0 l^1 k^2. com r r' A [k=0 i. ffill i (linvfill i x l)
                                      ;k=1 i. ffill i x
                                      ;l=0 i. rinvfill i (ffill i x) k
                                      ;l=1 i. ffill i x]
                                      x
-}

  CCoeAlong a r r' ->
    let ~x = u in coe r r' a x

  CCoeLinv0 a r r' ->
    let ~x   = u
        -- x = g (f x)
        ~lhs = coe r' r a (coe r r' a x)
        ~rhs = x
    in VPLam lhs rhs $ NICl j_ $ ICCoeLinv1 a r r' x

  CCoeRinv0 a r r' ->
    let ~x   = u
        -- f (g x) = x
        ~lhs = coe r r' a (coe r' r a x)
        ~rhs = x
    in VPLam lhs rhs $ NICl j_ $ ICCoeRinv1 a r r' x

  CCoeCoh0 a r r' ->
    let ~x = u

        -- (λ k. rinvfill a r r' (ffill a r r' x) k)
        ~lhs =
           -- coe r r' a (coe r' r a (coe r r' a x))
           let ~lhs' = coe r r' a (coe r' r a (coe r r' a x))
               ~rhs' = coe r r' a x in

           VPLam lhs' rhs' $ NICl k_ $ ICCoeCoh0Lhs a r r' x

        -- (λ k. coe r r' a x)
        ~rhs = refl (coe r r' a x)

    in VPLam lhs rhs $ NICl l_ $ ICCoeCoh1 a r r' x


-- | Apply an ivar closure.
icapp :: NCofArg => DomArg => NamedIClosure -> I -> Val
icapp (NICl _ t) arg = case t of

  ICEval s env rc t ->
    let ?env = env; ?sub = ext (wkSub s) arg; ?recurse = rc in eval t

  -- coe r r' (i. t i ={j. A i j} u i) p =
  --   λ {t r'}{u r'} j*. com r r' (i. A i j) [j=0 i. t i; j=1 i. u i] (p {t r} {u r}j)
  ICCoePath r r' a lhs rhs p ->
    let j = arg in
    hcom r r' (a ∙ r' ∙ j)
      (vshcons (eq j I0) i_ (\i -> coe i r' (bindI i_ \i -> a ∙ i ∙ j) (lhs ∙ i)) $
       vshcons (eq j I1) i_ (\i -> coe i r' (bindI i_ \i -> a ∙ i ∙ j) (rhs ∙ i)) $
       vshempty)
      (coe r r' (bindI i_ \i -> a ∙ i ∙ j) (papp (lhs ∙ r) (rhs ∙ r) p j))

  -- hcom r r' (lhs ={j.A j} rhs) [α i. t i] base =
  --   λ j*. hcom r r' (A j) [j=0 i. lhs; j=1 i. rhs; α i. t i j] (base j)
  ICHComPath r r' a lhs rhs sys p ->
    let j = arg in
    hcom r r' (a ∙ j)
      (vshcons (eq j I0) i_ (\_ -> lhs) $
       vshcons (eq j I1) i_ (\_ -> rhs) $
       mapVSysHCom (\i t -> papp lhs rhs (t ∙ i) j) (frc sys))
      (papp lhs rhs p j)

  -- hcom r r' ((j : A) → B j) [α i. t i] base =
  --   λ j*. hcom
  ICHComLine r r' a sys base ->
    let j = arg in
    hcom r r' (a ∙ j) (mapVSysHCom (\i t -> lapp (t ∙ i) j) (frc sys)) (lapp base j)

  ICCoeLine r r' a p ->
    let j = arg in
    coe r r' (bindI i_ \i -> a ∙ i ∙ j) (lapp p j)

  ICConst t -> t

  -- isEquiv : (A → B) → U
  -- isEquiv A B f :=
  --     (g^1    : B → A)
  --   × (linv^2 : (x^4 : A) → Path A (g (f x)) x)
  --   × (rinv^3 : (x^5 : B) → Path B (f (g x)) x)
  --   × (coh    : (x^6 : A) →
  --             PathP (i^7) (Path B (f (linv x {x}{g (f x)} i)) (f x))
  --                   (rinv (f x)))
  --                   (refl B (f x))

  ICIsEquiv7 b f g linv x ->
    let ~i   = arg
        ~fx  = f ∙ x
        ~gfx = g ∙ fx  in
    path b (f ∙ papp gfx x (linv ∙ x) i) fx

{-
  coeIsEquiv : (A : I → U) (r r' : I) → isEquiv (λ x. coe r r' A x)
  coeIsEquiv A r r' =

    ffill i x      := coe r i A x
    gfill i x      := coe i r A x
    linvfill i x j := hcom r i (A r) [j=0 k. x; j=1 k. coe k r A (coe r k A x)] x
    rinvfill i x j := hcom i r (A i) [j=0 k. coe k i A (coe i k A x); j=1 k. x] x

    g    := λ x^0. gfill r' x
    linv := λ x^0 j^1. linvfill r' x j
    rinv := λ x^0 j^1. rinvfill r' x j
    coh  := λ x^0 l^1 k^2. com r r' A [k=0 i. ffill i (linvfill i x l)
                                      ;k=1 i. ffill i x
                                      ;l=0 i. rinvfill i (ffill i x) k]
                                      ;l=1 i. ffill i x
                                      x
-}

  ICCoeLinv1 a r r' x ->
    let j = arg in linvfill a r r' x j

  ICCoeRinv1 a r r' x ->
    let j = arg in rinvfill a r r' x j

  ICCoeCoh1 a r r' x ->
    let l    = arg

        -- ffill a r r' (linvfill a r r' x l)
        ~lhs = ffill a r r' (linvfill a r r' x l)

        -- ffill a r r' x
        ~rhs = ffill a r r' x

    in VPLam lhs rhs $ NICl k_ $ ICCoeCoh2 a r r' x l

  ICCoeCoh2 a r r' x l ->
    let k = arg in
    coeCoherence a r r' x l k

  -- (λ k. rinvfill a r r' (ffill a r r' x) k)
  ICCoeCoh0Lhs a r r' x ->
    let k = arg in
    rinvfill a r r' (ffill a r r' x) k

-- | sym (A : U)(x y : A) -> x = y : y = x
--     := λ {y}{x} i*. hcom 0 1 A [i=0 j. p j; i=1 j. x] x;
  ICSym a x y p ->
    let i = frc arg in
    hcomd I0 I1 a
          (vshcons (eq i I0) j_ (\j -> papp x y p j) $
           vshcons (eq i I1) N_ (\_ -> x) $
           vshempty)
          x

-- | comp (A : U)(x y z : A) (p : x = y) (q : y = z) : x = z
--    := λ i*. hcom 0 1 A [i=0 j. x; i=1 j. q j] (p i);
  ICTrans a x y z p q ->
    let i = arg in
    hcomd I0 I1 a
      (vshcons (eq i I0) N_ (\_ -> x) $
       vshcons (eq i I1) j_ (\j -> papp y z q j) $
       vshempty)
      (papp x y p i)

-- | ap (A B : U)(f : A -> B)(x y : A)(p : x = y) : f x = f y
--     := λ i*. f (p i)
  ICAp f x y p ->
    let i = arg in f ∙ papp x y p i

  ICBindI a ->
    a ∙ arg

proj1' :: NCofArg => DomArg => Name -> Val -> Res
proj1' x t = case frc t of
  VPair _ t _ -> progress t
  VNe t       -> block $ VNe (NProj1 t x)
  v@VHole{}   -> block $ v
  VUnf t v v' -> block $ VUnf t (FProj1 x v) (proj1 x v')
  _           -> impossible

proj1 :: NCofArg => DomArg => Name -> Val -> Val
proj1 x t = (proj1' x t)^.val

proj2' :: NCofArg => DomArg => Name -> Val -> Res
proj2' x t = case frc t of
  VPair _ _ u -> progress u
  VNe t       -> block $ VNe (NProj2 t x)
  v@VHole{}   -> block $ v
  VUnf i v v' -> block $ VUnf i (FProj2 x v) (proj2 x v')
  _           -> impossible

proj2 :: NCofArg => DomArg => Name -> Val -> Val
proj2 x t = (proj2' x t)^.val

unpack' :: NCofArg => DomArg => Name -> Val -> Res
unpack' x t = case frc t of
  VPack _ t   -> progress t
  VNe t       -> block $ VNe (NUnpack t x)
  v@VHole{}   -> block $ v
  VUnf i v v' -> block $ VUnf i (FUnpack v x) (unpack x v')
  _           -> impossible

unpack :: NCofArg => DomArg => Name -> Val -> Val
unpack x v = (unpack' x v)^.val

-- | Path application.
papp' :: NCofArg => DomArg => Val -> Val -> Val -> I -> Res
papp' ~l ~r ~t i = case frc i of
  I0     -> progress l
  I1     -> progress r
  i@(IVar x) -> case frc t of
    VPLam _ _ t   -> progress (t ∙ IVar x)
    VNe t         -> block $ VNe (NPApp l r t i)
    v@VHole{}     -> block $ v
    VUnf inf t t' -> block $ VUnf inf (FPApp l r t i) (papp l r t' i)
    _             -> impossible

papp :: NCofArg => DomArg => Val -> Val -> Val -> I -> Val
papp ~l ~r ~t i = (papp' l r t i)^.val

lapp' :: NCofArg => DomArg => Val -> I -> Res
lapp' t i = case frc t of
  VLLam t       -> progress $ t ∙ i
  VNe t         -> block $ VNe (NLApp t i)
  v@VHole{}     -> block $ v
  VUnf inf t t' -> block $ VUnf inf (FLApp t i) (lapp t' i)
  _             -> impossible

lapp :: NCofArg => DomArg => Val -> I -> Val
lapp t i = (lapp' t i)^.val

coed' :: I -> I -> BindI Val -> Val -> NCofArg => DomArg => Res
coed' r r' topA t = case (frc topA) ^. body of

  VPi (rebind topA -> a) (rebind topA -> b) ->
    progress $
    VLam $ NCl (b^.body.name) $ CCoePi r r' a b t

  -- coe r r' (i. (x : A i) × B i x) t =
  -- (coe r r' A t.1, coe r r' (i. B i (coe r i A t.1)) t.2)
  VSg (rebind topA -> a) (rebind topA -> b) ->
    let t1 = proj1 (b^.body.name) t
        t2 = proj2 (b^.body.name) t

    in progress $
      VPair (b^.body.name)
             (coed r r' a t1)
             (coed r r' (bindI j_ \j -> b ∙ j ∙ coe r j a t1) t2)

  VPath (rebind topA -> a) (rebind topA -> lhs) (rebind topA -> rhs) ->
    progress $
        VPLam (lhs ∙ r') (rhs ∙ r')
      $ NICl (a^.body.name)
      $ ICCoePath r r' a lhs rhs t

  VLine (rebind topA -> a) ->
    progress $
        VLLam
      $ NICl (a^.body.name)
      $ ICCoeLine r r' a t

  VU ->
    progress t

  -- closed inductives
  VTyCon x ENil ->
    progress t

  a@(VTyCon x (rebind topA -> ps)) -> case frc t of
    VDCon dci sp ->
      progress $ VDCon dci (coeindsp r r' ps sp (dci^.fieldTypes))
    t@(VNe _) ->
      block $ VNe (NCoe r r' (rebind topA a) t)
    VUnf inf t t' ->
      let abind = rebind topA a
      in block $ VUnf inf (FCoeVal r r' abind t) (coed r r' abind t')
    t@(VHCom _ _ _ _ _) ->
      block $ VNe (NCoe r r' (rebind topA a) t)
    v@VHole{} ->
      block v
    _ ->
      impossible

  a@(VNe _) ->
    block $ VNe (NCoe r r' (rebind topA a) t)

  VUnf inf (rebind topA -> a) (rebind topA -> a') ->
    block $ VUnf inf (FCoeTy r r' a t) (coed r r' a' t)


{-
- coe Glue with unfolded and optimized hcom over fibers


coe r r' (i. Glue (A i) [(α i). (T i, f i)]) gr =

  Ar' = A r'
  sysr = [(α r). (T r, f r)]    -- instantiate system to r

  ar' : Ar'
  ar' := gcom r r' (i. A i) [(∀i.α) i. f i (coe r i (i.T i) gr)] (unglue gr sysr)

  working under (α r'), mapping over the [(α r'). (T r', f r')] system, producing two output systems:

    Tr' = T r'

    fr' : Tr' ≃ Ar'
    fr' = f r'

    fibval : Tr'
    fibval = fr'⁻¹ ar'

    fibpath : fr' fibval = ar'
    fibpath = fr'.rinv ar'

    -- in the nested (∀i.α) here, we take the T from the original component of the
    -- mapped-over [(α i). (T i, f i)] system

    valSys = [r=r'  i. fr'.linv gr i
            ;(∀i.α) i. fr'.linv (coe r r' (i. T i) gr) i]

    fibval* : Tr'
    fibval* = ghcom 0 1 Tr' valSys fibval

    -- this should be a metatheoretic (I → Ar') function, because we only need it applied
    -- to the "j" variable in the end result. For clarity though, it's good to write it as a path here.

    fibpath* : fr' fibval = ar'
    fibpath* = λ j.
       hcom 0 1 Ar' [j=0    i. fr' (ghcom 0 i Tr' valSys fibval)    -- no need to force valSys because
                    ;j=1    i. ar'                                  -- it's independent from j=0
                    ;r=r'   i. fr'.coh gr i j
                    ;(∀i.α) i. fr'.coh (coe r r' (i. T i) gr) i j]
                    (fibpath {fr' fibval} {ar'} j)

    -- one output system is a NeSys containing fibval*
    -- the other is NeSysHCom with fibpath* applied to the binder

  Result :=
    glue (hcom 1 0 Ar' [r=r' j. unglue gr sysr; αr' j. fibpath* j] ar')
         [αr'. fibval*]

-}

  VGlueTy (rebind topA -> a) (rebind topA -> topSys) -> let

    gr           = t
    _Ar'         = a ∙ r'
    ~topSysr     = topSys ∙ r  :: NeSys
    topSysr'     = topSys ∙ r' :: NeSys
    forallTopSys = forallNeSys topSys
    topSysr'f    = frc topSysr'

  -- ar' : Ar'
  -- ar' := gcom r r' (i. A i) [(∀i.α) i. f i (coe r i (j. T j) gr)] (unglue gr sysr)
    ~ar' = ghcomdn r r' _Ar'
             (mapNeSysHCom
                (\i tf -> coe i r' a (  proj1 f_ (proj2 ty_ (tf ∙ i))
                                      ∙ coe r i (proj1BindIFromLazy ty_ tf) gr))
                forallTopSys)
             (coed r r' a (unglue gr (frc topSysr)))

    mkComponent :: NCofArg => Val -> (Val, BindILazy Val)
    mkComponent tfr' = let

      equiv1   = tfr'
      equiv2   = proj2 ty_   equiv1
      equiv3   = proj2 f_    equiv2
      equiv4   = proj2 g_    equiv3
      ~equiv5  = proj2 linv_ equiv4

      tr'      = proj1 ty_   equiv1
      fr'      = proj1 f_    equiv2
      fr'inv   = proj1 g_    equiv3
      ~r'linv  = proj1 linv_ equiv4
      ~r'rinv  = proj1 rinv_ equiv5
      ~r'coh   = unpack coh_ (proj2 rinv_ equiv5)

      ~fibval  = fr'inv ∙ ar'
      ~fibpath = r'rinv ∙ ar'

      ~forallTopSysf = frc forallTopSys

      -- shorthands for path applications
      app_r'linv :: NCofArg => Val -> I -> Val
      app_r'linv ~x i =
        papp (fr'inv ∙ (fr' ∙ x)) x (r'linv ∙ x) i

      app_r'coh :: NCofArg => Val -> I -> I -> Val
      app_r'coh ~x i j =
        papp (fr' ∙ app_r'linv x i)
             (fr' ∙ x)
             (papp (r'rinv ∙ (fr' ∙ x)) (refl (fr' ∙ x)) (r'coh ∙ x) i)
             j

      -- valSys should be fine without NCof polymorphism

      -- valSys = [r=r'  i. fr'.linv gr i
      --         ;(∀i.α) i. fr'.linv (coe r r' (i. T i) gr) i]
      ~valSys =
          vshcons (eq r r') i_ (\i -> app_r'linv gr i) $
          mapVSysHCom (\i tf -> app_r'linv (coe r r' (proj1BindIFromLazy ty_ tf) gr) i) $
          forallTopSysf


      -- fibval* : Tr'
      -- fibval* = ghcom 0 1 Tr' valSys fibval
      ~fibval' = ghcomd I0 I1 tr' valSys fibval

      -- fibpath* : fr' fibval = ar'
      -- fibpath* = λ j.
      --   ghcom 0 1 Ar' [j=0    i. fr' (ghcom 0 i Tr' valSys fibval)    -- no need to force valSys because
      --                 ;j=1    i. ar'                                  -- it's independent from j=0
      --                 ;r=r'   i. fr'.coh gr i j
      --                 ;(∀i.α) i. fr'.coh (coe r r' (i. T i) gr) i j]
      --                 (fibpath {fr' fibval} {ar'} j)

      fibpath' =
        bindILazy j_ \j ->
        hcomd I0 I1 _Ar'
          (vshcons (eq j I0) i_ (\i -> fr' ∙ ghcom I0 i tr' valSys fibval) $
           vshcons (eq j I1) i_ (\i -> ar') $
           vshcons (eq r r') i_ (\i -> app_r'coh gr i j) $
           mapVSysHCom (\i tf -> app_r'coh (coe r r' (proj1BindIFromLazy ty_ tf) gr) i j) $
           forallTopSysf
          )
          (papp (fr' ∙ fibval) ar' fibpath j)

      in (fibval', fibpath')

    mkNeSystems :: NeSys -> (NeSys, NeSysHCom)
    mkNeSystems = \case
      NSEmpty         -> NSEmpty // NSHEmpty
      NSCons tfr' sys -> let
        alphar' = tfr'^.binds
        (fibval  , !fibpath)  = assumeCof alphar' $ mkComponent (tfr'^.body)
        (!fibvals, !fibpaths) = mkNeSystems sys
        in NSCons (BindCofLazy alphar' fibval) fibvals // NSHCons (BindCof alphar' fibpath) fibpaths

    (!fibvals, !fibpaths) = case topSysr'f of
      VSTotal tfr'   -> let
        (!fibval, !fibpath) = mkComponent tfr'
        in VSTotal fibval // VSHTotal fibpath
      VSNe sys -> let
        (!fibvals, !fibpaths) = mkNeSystems sys
        in VSNe fibvals // VSHNe fibpaths

    -- glue (hcom 1 0 Ar' [r=r' j. unglue gr sysr; αr' j. fibpath* j] ar')
    --      [αr'. fibval*]
    in progress $
        glue
         (hcomd I1 I0 _Ar' (vshcons (eq r r') i_ (\i -> unglue gr (frc topSysr)) fibpaths) ar')
         topSysr'f
         fibvals

  -- coe r r' (i. Wrap x (a i)) t = pack (coe r r' (i. a i) (t.unpackₓ))
  VWrap x (rebind topA -> a) ->
    progress $ VPack x $ coed r r' a (unpack x t)

  VHTyCon _ ENil ->
    progress t

  a@(VHTyCon ti (rebind topA -> ps)) -> case frc t of

    t@(VHDCon di _ fs s) ->
      let psr' = ps ∙ r' in
      if di^.isCoherent then
        progress $ VHDCon di psr' (coeindsp r r' ps fs (di^.fieldTypes)) s
      else
        case coehindsp r r' (rebind topA a) ps fs (di^.fieldTypes) s (di^.boundary) of
          (!sp, !sys) -> progress $
            VHCom r' r (VHTyCon ti psr')
              sys
              (VHDCon di psr' sp s)

    -- coe r r' a (fhcom i j (a r) [α k. t k] b) =
    -- fhcom i j (a r') [α k. coe r r' a (t k)] (coe r r' a b)
    t@(VHCom i j _ sys b) ->
      let abind = rebind topA a in
      progress $ VHCom i j
        (VHTyCon ti (ps ∙ r'))
        (mapNeSysHCom (\k t -> coe r r' abind (t ∙ k)) sys)
        (coed r r' abind b)

    t@(VNe n) ->
      block $ VNe (NCoe r r' (rebind topA a) t)

    VUnf inf t t' ->
      let abind = rebind topA a in
      block $ VUnf inf (FCoeVal r r' abind t) (coed r r' abind t')

    t@VHole{} ->
      block t

    v -> impossible

  v@VHole{} -> block v

  v ->
    impossible

coed :: I -> I -> BindI Val -> Val -> NCofArg => DomArg => Val
coed r r' topA t = (coed' r r' topA t)^.val

coe' :: NCofArg => DomArg => I -> I -> BindI Val -> Val -> Res
coe' r r' ~a t
  | frc r == frc r' = progress t
  | True            = coed' r r' a t
{-# inline coe #-}

coe :: NCofArg => DomArg => I -> I -> BindI Val -> Val -> Val
coe r r' ~a t = (coe' r r' a t)^.val

-- | HCom with off-diagonal I args ("d") and neutral system arg ("n").
hcomdn' :: I -> I -> Val -> NeSysHCom -> Val -> NCofArg => DomArg => Res
hcomdn' r r' topA nts base =
 case runIO (do{bumpHCom' (isEmptyNSH nts); pure $! frc topA}) of
  VPi a b ->
    progress $
    VLam $ NCl (b^.name) $ CHComPi r r' a b nts base

  VSg a b ->
    progress $
    VPair
      (b^.name)
      (hcomdn r r' a
        (mapNeSysHCom (\i t -> proj1 (b^.name) (t ∙ i)) nts)
        (proj1 (b^.name) base))

      (hcomdn r r'
        (b ∙ hcomdn r r' a
             (mapNeSysHCom (\i t -> proj1 (b^.name) (t ∙ i)) nts)
             (proj1 (b^.name) base))

        (mapNeSysHCom
          (\i t ->
           coe i r'
             (bindI i_ \i ->
                b ∙ hcom r i a
                     (mapVSysHCom (\i t -> proj1 (b^.name) (t ∙ i)) (frc nts))
                     (proj1 (b^.name) base))
             (proj2 (b^.name) (t ∙ i)))
          nts)

        (coed r r'
           (bindI i_ \i ->
              b ∙ hcomn r i a
                   (mapNeSysHCom (\i t -> proj1 (b^.name) (t ∙ i)) nts)
                   (proj1 (b^.name) base))
           (proj2 (b^.name) base)))

  -- (  hcom r r' A [α i. (t i).1] b.1
  --  , com r r' (i. B (hcom r i A [α j. (t j).1] b.1)) [α i. (t i).2] b.2)

  VPath a lhs rhs ->
    progress $
        VPLam lhs rhs
      $ NICl (a^.name)
      $ ICHComPath r r' a lhs rhs nts base

  a@(VNe n) ->
    block $ VHCom r r' a nts base

  VUnf inf a a' ->
    block $ VUnf inf (FHComTy r r' a nts base) (hcomdn r r' a' nts base)

  -- hcom r r' U [α i. t i] b =
  --   Glue b [r=r'. (b, idEquiv); α. (t r', (coe r' r (i. t i), coeIsEquiv))]

  VU -> let

    -- NOTE: r = r' can be false or neutral
    sys = nscons (eq r r') (VPair ty_ base (theIdEquiv base)) $
          mapNeSysFromH
            (\t -> VPair ty_ (t ∙ r') (theCoeEquiv (bindIFromLazy t) r' r))
            nts

    in progress $ VGlueTy base sys

-- hcom for Glue
--------------------------------------------------------------------------------

  -- hcom r r' (Glue [α. (T, f)] A) [β i. t i] gr =
  --   glue (hcom r r' A [β i. unglue (t i); α i. f (hcom r i T [β j. t j] gr)] (unglue gr))
  --        [α. hcom r r' T [β i. t i] gr]

  VGlueTy a alphasys ->
    let gr      = base
        betasys = nts

            -- [α. hcom r r' T [β i. t i] gr]
        fib = mapNeSys (\t -> hcom r r' (proj1 ty_ t) (frc betasys) gr) alphasys

        -- hcom r r' A [  β i. unglue (t i)
        --              ; α i. f (hcom r i T [β. t] gr)]
        --             (unglue gr)
        hcombase =
          hcomdn r r' a
            (catNeSysHCom
               (mapNeSysHCom (\i t -> unglue (t ∙ i) (frc alphasys)) betasys)
               (mapNeSysToH  (\i tf -> proj1 f_ (proj2 ty_ tf)
                                      ∙ hcom r i (proj1 ty_ tf) (frc betasys) gr) alphasys))
            (ungluen gr alphasys)

    in progress $ VGlue hcombase alphasys fib

  VLine a ->
    progress $
        VLLam
      $ NICl (a^.name)
      $ ICHComLine r r' a nts base

  -- hcom r r' (x : A) [β i. t i] base =
  --   pack (hcom r r' A [β i. (t i).unpackₓ] (base.unpackₓ))
  VWrap x a ->
    progress $
    VPack x $ hcomdn r r' a
      (mapNeSysHCom (\i t -> unpack x (t ∙ i)) nts)
      (unpack x base)

  a@(VTyCon _ ps) -> case frc base of
    base@(VDCon dci sp) -> case ?dom of
      0 -> progress $
        VDCon dci (hcomind0sp r r' a nts ps (dci^.conId) 0 sp (dci^.fieldTypes))
      _ -> case projsys' (dci^.conId) nts of
        TTPProject prj  ->
          progress $
          VDCon dci (hcomindsp r r' a prj ps (dci^.conId) 0 sp (dci^.fieldTypes))
        TTPNe sys ->
          block $ VHCom r r' a sys base

    base@(VNe n) ->
      block $ VHCom r r' a nts base

    VUnf inf base base' ->
      block $ VUnf inf (FHComVal r r' a nts base) (hcomdn r r' a nts base')

    base@(VHCom _ _ _ _ _) ->
      block $ VHCom r r' a nts base

    base@VHole{} -> block base
    _            -> impossible


  -- "fhcom", hcom on HITs is blocked
  a@(VHTyCon tyinf ps) ->
    block $ VHCom r r' a nts base

  v@VHole{} -> block v

  _ ->
    impossible

hcomdn :: I -> I -> Val -> NeSysHCom -> Val -> NCofArg => DomArg => Val
hcomdn r r' topA nts base = (hcomdn' r r' topA nts base)^.val

----------------------------------------------------------------------------------------------------

-- | HCom with nothing known about semantic arguments.
hcom' :: NCofArg => DomArg => I -> I -> Val -> VSysHCom -> Val -> Res
hcom' r r' ~a ~t ~b
  | frc r == frc r' = runIO (bumpHCom >> (pure $! progress b))
  | True = case t of
      VSHTotal v -> runIO (bumpHCom >> (pure $! progress $ v ∙ r'))
      VSHNe sys  -> hcomdn' r r' a sys b
{-# inline hcom #-}

hcom :: NCofArg => DomArg => I -> I -> Val -> VSysHCom -> Val -> Val
hcom r r' ~a ~t ~b = (hcom' r r' a t b)^.val

-- | HCom with neutral system input.
hcomn :: NCofArg => DomArg => I -> I -> Val -> NeSysHCom -> Val -> Val
hcomn r r' ~a ~sys ~b
  | frc r == frc r' = runIO (bumpHCom >> pure b)
  | True            = hcomdn r r' a sys b
{-# inline hcomn #-}

-- | Off-diagonal HCom.
hcomd :: NCofArg => DomArg => I -> I -> Val -> VSysHCom -> Val -> Val
hcomd r r' ~a sys ~b = case sys of
  VSHTotal v -> runIO (bumpHCom >> (pure $! v ∙ r'))
  VSHNe sys  -> hcomdn r r' a sys b
{-# inline hcomd #-}


-- ghcom
----------------------------------------------------------------------------------------------------

-- | Off-diagonal ghcom with neutral system input.
--   See: https://carloangiuli.com/papers/thesis.pdf  Figure 4.2
ghcomdn :: NCofArg => DomArg => I -> I -> Val -> NeSysHCom -> Val -> Val
ghcomdn r r' a topSys base = case topSys of

  NSHEmpty ->
    runIO (bumpHCom >> pure base)

  NSHCons t sys -> case t^.binds of
    NCEq i j ->
      hcomd r r' a
        (vshcons (eq i I0) z_ (\z ->
           hcom r z a (vshcons (eq j I0) (t^.body.name) (\y ->
                          (t^.body) ∙ y) $
                       vshcons (eq j I1) (t^.body.name) (\y ->
                          ghcom r y a (frc sys) base) $
                       frc sys)
                      base) $
         vshcons (eq i I1) z_ (\z ->
           hcom r z a (vshcons (eq j I1) (t^.body.name) (\y ->
                         (t^.body) ∙ y) $
                       vshcons (eq j I0) (t^.body.name) (\y ->
                         ghcom r y a (frc sys) base) $
                       frc sys)
                      base) $
         VSHNe topSys)
        base

-- | Off-diagonal ghcom.
ghcomd :: NCofArg => DomArg => I -> I -> Val -> VSysHCom -> Val -> Val
ghcomd r r' ~a sys ~base = case sys of
  VSHTotal v -> runIO (bumpHCom >> (pure $! v ∙ r'))
  VSHNe sys  -> ghcomdn r r' a sys base
{-# inline ghcomd #-}

ghcom :: NCofArg => DomArg => I -> I -> Val -> VSysHCom -> Val -> Val
ghcom r r' ~a ~sys ~b
  | frc r == frc r' = runIO (bumpHCom >> pure b)
  | True            = ghcomd r r' a sys b
{-# inline ghcom #-}

--------------------------------------------------------------------------------

glueTy' :: NCofArg => DomArg => Val -> VSys -> Res
glueTy' ~a sys = case sys of
  VSTotal b -> progress $ proj1 ty_ b
  VSNe sys  -> block    $ VGlueTy a sys
{-# inline glueTy #-}

glueTy :: NCofArg => DomArg => Val -> VSys -> Val
glueTy ~a sys = (glueTy' a sys)^.val

glue' :: Val -> VSys -> VSys -> Res
glue' ~t eqs sys = case (eqs, sys) of
  (VSTotal{}, VSTotal v) -> progress v
  (VSNe eqs , VSNe sys)  -> block $ VGlue t eqs sys
  _                      -> impossible
{-# inline glue #-}

glue :: Val -> VSys -> VSys -> Val
glue ~t eqs sys = (glue' t eqs sys)^.val

unglue' :: NCofArg => DomArg => Val -> VSys -> Res
unglue' ~t sys = case sys of
  VSTotal teqv -> progress $ proj1 f_ (proj2 ty_ teqv) ∙ t
  VSNe sys     -> ungluen' t sys
{-# inline unglue #-}

unglue :: NCofArg => DomArg => Val -> VSys -> Val
unglue ~t sys = (unglue' t sys)^.val

-- | Unglue with neutral system arg.
ungluen' :: NCofArg => DomArg => Val -> NeSys -> Res
ungluen' t sys = case frc t of
  VGlue base _ _          -> progress base
  VNe n                   -> block $ VNe (NUnglue n sys)
  VUnf inf t t'           -> block $ VUnf inf (FUnglue t sys) (ungluen t' sys)
  v@VHole{}               -> block $ v
  _                       -> impossible

ungluen :: NCofArg => DomArg => Val -> NeSys -> Val
ungluen t sys = (ungluen' t sys)^.val


-- Strict inductive types
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

evalIndParam :: NCofArg => DomArg => Env -> Tm -> Val
evalIndParam env t =
  let ?sub     = emptySub (dom ?cof)
      ?recurse = DontRecurse
      ?env     = env
  in eval t
{-# inline evalIndParam #-}

goParams :: EvalArgs (Env -> Spine -> Env)
goParams env = \case
  SPNil       -> env
  SPCons a as -> goParams (EDef env (eval a)) as

params :: EvalArgs (Spine -> Env)
params = goParams ENil

goLazyParams :: EvalArgs (Env -> LazySpine -> Env)
goLazyParams env = \case
  LSPNil       -> env
  LSPCons a as -> goLazyParams (EDef env (eval a)) as

lazyParams :: EvalArgs (LazySpine -> Env)
lazyParams = goLazyParams ENil

spine :: EvalArgs (Spine -> VDSpine)
spine = \case
  SPNil       -> VDNil
  SPCons t ts -> VDCons (eval t) (spine ts)

recursiveCall :: RecurseArg => RecInfo -> Val
recursiveCall inf = case ?recurse of
  Recurse v   -> coerce v
  DontRecurse -> VNe (NDontRecurse inf)
{-# inline recursiveCall #-}

pushVars :: DomArg => Env -> [Name] -> (Env, Lvl)
pushVars env = \case
  []   -> (env // ?dom)
  _:ns -> fresh \v -> pushVars (EDef env v) ns

-- -- TODO: refactor "push" functions like this below, try to only
-- --       use the generic "fresh" functions.
-- pushIVars :: NCofArg => Sub -> [Name] -> (Sub, NCof)
-- pushIVars s is = let ?sub = s in freshIVarsS is (?sub // ?cof)

pushIVars :: NCofArg => Sub -> [Name] -> (Sub, NCof)
pushIVars s = \case
  []   -> (s // ?cof)
  _:is -> freshI \v -> pushIVars (wkSub s `ext` v) is

pushSp :: Env -> VDSpine -> Env
pushSp env = \case
  VDNil       -> env
  VDCons v sp -> pushSp (EDef env v) sp

lookupCase :: EvalArgs (Lvl -> VDSpine -> Cases -> Res)
lookupCase i sp cs = case i // cs of
  (0, CSCons _ _  body cs) -> let ?env = pushSp ?env sp in progress $ eval body
  (i, CSCons _ _  _    cs) -> lookupCase (i - 1) sp cs
  _                        -> impossible

case_' :: NCofArg => DomArg => Val -> NamedClosure -> EvalClosure Cases -> Res
case_' t b ecs@(EC sub env rc cs) = case frc t of
  VDCon dci sp         -> let ?sub = wkSub sub; ?env = env; ?recurse = rc
                          in lookupCase (dci^.conId) sp cs
  n@(VNe _)            -> block $ VNe (NCase n b ecs)
  VUnf inf t t'        -> block $ VUnf inf (FCase_ t b ecs) (case_ t' b ecs)
  n@(VHCom _ _ _ _ _ ) -> block $ VNe (NCase n b ecs)
  v@VHole{}            -> block $ v
  _                    -> impossible

case_ :: NCofArg => DomArg => Val -> NamedClosure -> EvalClosure Cases -> Val
case_ t b ecs = (case_' t b ecs)^.val

projVDSpine :: Lvl -> VDSpine -> Val
projVDSpine x sp = case (x, sp) of
  (0, VDCons t _ ) -> t
  (x, VDCons _ sp) -> projVDSpine (x - 1) sp
  _                -> impossible

lazyprojfield :: NCofArg => DomArg => Lvl -> Lvl -> Val -> Val
lazyprojfield conid fieldid v = case frc v of
  VDCon dci sp | conid == (dci^.conId) -> projVDSpine fieldid sp

  -- we drop the Unf here because there's no simple syntactic representation of
  -- lazy field projection that could be Frozen.
  VUnf _ _ v'                          -> lazyprojfield conid fieldid v'
  _                                    -> impossible
-- {-# inline lazyprojfield #-}

lazyprojsys :: NCofArg => DomArg => Lvl -> Lvl -> NeSysHCom -> NeSysHCom
lazyprojsys conid fieldid = \case
  NSHEmpty      -> NSHEmpty
  NSHCons t sys -> NSHCons (mapBindCof t \t -> umapBindILazy t (\_ -> lazyprojfield conid fieldid))
                           (lazyprojsys conid fieldid sys)

hcomind0sp :: NCofArg => DomArg => I -> I -> Val -> NeSysHCom
           -> Env -> Lvl -> Lvl -> VDSpine -> Tel -> VDSpine
hcomind0sp r r' a sys params conid fieldid sp fieldtypes = case (sp, fieldtypes) of
  (VDNil, TNil) ->
    VDNil
  (VDCons t sp, TCons _ tty fieldtypes) ->
    VDCons (hcomdn r r' (evalIndParam params tty) (lazyprojsys conid fieldid sys) t)
           (hcomind0sp r r' a sys (EDef params t) conid (fieldid + 1) sp fieldtypes)
  _ ->
    impossible

-- System where all components are known to be the same constructor
data Projected
  = PNil
  | PCons NeCof Name IVar VDSpine Projected
  deriving Show

-- TODO: unbox
data TryToProject
  = TTPProject Projected
  | TTPNe NeSysHCom
  deriving Show

projsys :: NCofArg => DomArg => Lvl -> NeSysHCom -> NeSysHCom -> TryToProject
projsys conid topSys = \case
  NSHEmpty      -> TTPProject PNil
  NSHCons t sys ->
    let ~prj = projsys conid topSys sys; {-# inline prj #-} in

    assumeCof (t^.binds) $ case (frc (t^.body))^.body of
      VDCon dci sp | conid == dci^.conId ->
        case prj of
          TTPProject prj ->
            TTPProject (PCons (t^.binds) (t^.body.name) (t^.body.binds) sp prj)
          prj@TTPNe{} ->
            prj

      -- NOTE: extend blockers with neutral's ivars BUT DELETE BOUND VAR.
      VNe _ ->
        TTPNe topSys

      VUnf _ _ _ ->
        error "TODO: unfolding in system projection"

      -- likewise
      VHCom _ _ _ _ _ ->
        TTPNe topSys

      VHole{} -> error "TODO: hole in system projection"
      _       -> impossible

projsys' :: NCofArg => DomArg => Lvl -> NeSysHCom -> TryToProject
projsys' conix sys = projsys conix sys sys
{-# inline projsys' #-}

projfields :: Projected -> Lvl -> NeSysHCom
projfields prj fieldid = case prj of
  PNil                  -> NSHEmpty
  PCons ncof x i sp prj -> NSHCons (BindCof ncof (BindILazy x i (projVDSpine fieldid sp)))
                                   (projfields prj fieldid)

hcomindsp :: NCofArg => DomArg => I -> I -> Val -> Projected -> Env -> Lvl -> Lvl -> VDSpine -> Tel -> VDSpine
hcomindsp r r' a prj params conid fieldid sp fieldtypes = case (sp, fieldtypes) of
  (VDNil, TNil) ->
    VDNil
  (VDCons t sp, TCons _ tty fieldtypes) ->
    VDCons (hcomdn r r' (evalIndParam params tty) (projfields prj fieldid) t)
           (hcomindsp r r' a prj (EDef params t) conid (fieldid + 1) sp fieldtypes)
  _ ->
    impossible

coeindsp :: I -> I -> BindI Env -> VDSpine -> Tel ->  NCofArg => DomArg =>  VDSpine
coeindsp r r' params sp fieldtypes = case (sp, fieldtypes) of
  (VDNil, TNil) -> VDNil
  (VDCons t sp, TCons _ tty fieldtypes) ->
    let tty' = umapBindI params \_ ps -> evalIndParam ps tty in
    VDCons (coed r r' tty' t)
           (coeindsp r r' (mapBindI params \i ps -> EDef ps (coe r i tty' t)) sp fieldtypes)
  _ -> impossible


-- Higher inductive types
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- TODO: unbox
data VBoundary = VBTotal Val | VBNe deriving Show

vbempty :: VBoundary
vbempty = VBNe

vbcons :: NCofArg => VCof -> (NCofArg => Val) -> VBoundary -> VBoundary
vbcons cof v ~sys = case cof of
  VCTrue  -> VBTotal v
  VCFalse -> sys
  VCNe _  -> sys
{-# inline vbcons #-}

evalBoundary :: EvalArgs (Sys -> VBoundary)
evalBoundary = \case
  SEmpty          -> vbempty
  SCons cof t sys -> vbcons (evalCof cof) (eval t) (evalBoundary sys)

hdcon' :: NCofArg => DomArg => HDConInfo -> Env -> VDSpine -> Sub -> Res
hdcon' inf ps fs s = case inf^.boundary of
  SEmpty -> block $ VHDCon inf ps fs s
  bnd    -> let ?sub = s; ?env = pushSp ps fs; ?recurse = DontRecurse in
            case evalBoundary bnd of
              VBTotal v -> progress v
              VBNe      -> block $ VHDCon inf ps fs s
{-# inline hdcon #-}

hdcon :: NCofArg => DomArg => HDConInfo -> Env -> VDSpine -> Sub -> Val
hdcon inf ps fs s = (hdcon' inf ps fs s)^.val

lookupHCase :: EvalArgs (Lvl -> VDSpine -> Sub -> HCases -> Res)
lookupHCase i sp s cs = case i // cs of
  (0, HCSCons _ _ _ body cs) -> let ?env = pushSp ?env sp; ?sub = pushSub ?sub s in
                                progress $ eval body
  (i, HCSCons _ _ _ _    cs) -> lookupHCase (i - 1) sp s cs
  _                          -> impossible

sysCofs :: NeSys -> [NeCof]
sysCofs = \case
  NSEmpty -> []
  NSCons t cs -> t^.binds : sysCofs cs

hcase' :: Val -> NamedClosure -> EvalClosure HCases -> NCofArg => DomArg => Res
hcase' t b ecs@(EC sub env rc cs) = case frc t of

  VHDCon i ps fs s ->
    let ?sub = wkSub sub; ?env = env; ?recurse = rc in
    lookupHCase (i^.conId) fs s cs

  t@(VHCom r r' a sys base) ->

     -- case (hcom r r' a [α i. t i] base) B cs =
     -- let B* = λ i. B (hcom r i a [α i. t i] base);
     -- hcom r r' (B (hcom r r' a [α i. t i] base))
     --           [α i. coe i r' B* (case (t i) B cs)]
     --           (coe r r' B* (case base B cs))
    let bbind = bindI i_ \i -> b ∙ hcom r i a (frc sys) base in

    progress $
    hcomdn r r' (b ∙ t)
      (mapNeSysHCom (\i t -> coe i r' bbind (hcase (t ∙ i) b ecs)) sys)
      (coed r r' bbind (hcase base b ecs))

  n@(VNe _)     -> block $ VNe (NHCase n b ecs)
  VUnf inf t t' -> block $ VUnf inf (FHCase_ t b ecs) (hcase t' b ecs)
  v@VHole{}     -> block $ v
  v             -> impossible

hcase :: Val -> NamedClosure -> EvalClosure HCases -> NCofArg => DomArg => Val
hcase t b ecs = (hcase' t b ecs)^.val

evalCoeBoundary :: EvalArgs (I -> IVar -> BindI VTy -> Sys -> NeSysHCom)
evalCoeBoundary r' i a = \case
  SEmpty ->
    NSHEmpty
  SCons cof t bnd -> case evalCof cof of
    VCTrue   -> impossible
    VCFalse  -> evalCoeBoundary r' i a bnd
    VCNe cof -> NSHCons (bindCof cof (BindILazy (a^.name) i (coe (IVar i) r' a (eval t))))
                        (evalCoeBoundary r' i a bnd)

coehindsp ::
   I -> I -> BindI VTy -> BindI Env -> VDSpine -> Tel -> Sub -> Sys -> NCofArg => DomArg => (VDSpine, NeSysHCom)
coehindsp r r' topA params sp fieldtypes s boundary = case (sp, fieldtypes) of
  (VDNil, TNil) ->
    let nesys = (mapBindIVar params \i ps -> let ?env = ps; ?sub = s; ?recurse = DontRecurse
                                             in evalCoeBoundary r' i topA boundary)^.body in
    (VDNil // nesys)

  (VDCons t sp, TCons _ tty fieldtypes) ->
    let tty' = umapBindI params \_ ps -> evalIndParam ps tty in
    case coehindsp r r' topA (mapBindI params \i ps -> EDef ps (coe r i tty' t)) sp fieldtypes s boundary of
      (!sp, !sys) -> VDCons (coed r r' tty' t) sp // sys
  _ ->
    impossible

----------------------------------------------------------------------------------------------------

evalClosure :: EvalArgs (Name -> Tm -> NamedClosure)
evalClosure x a = NCl x (CEval (EC ?sub ?env ?recurse a))
{-# inline evalClosure #-}

evalClosureLazy :: EvalArgs (Name -> Tm -> NamedClosure)
evalClosureLazy x ~a = NCl x (CEvalLazy (ECL ?sub ?env ?recurse a))
{-# inline evalClosureLazy #-}

evalIClosure :: EvalArgs (Name -> Tm -> NamedIClosure)
evalIClosure x a = NICl x (ICEval ?sub ?env ?recurse a)
{-# inline evalIClosure #-}

topVar :: DefInfo -> Val
topVar inf = case inf of
  DI _ _ v _ _ _ _ True -> v
  DI _ _ v _ _ _ _ _    -> VUnf inf (FTopVar inf) v
{-# inline topVar #-}

eval :: EvalArgs (Tm -> Val)
eval = \case

  TopVar inf _       -> topVar inf
  RecursiveCall inf  -> recursiveCall inf
  LocalVar x         -> localVar x
  Let x _ t u        -> define (eval t) (eval u)

  -- Inductives
  TyCon i ts         -> VTyCon i (params ts)
  DCon i sp          -> VDCon i (spine sp)
  Case t x b cs      -> case_ (eval t) (evalClosureLazy x b) (EC ?sub ?env ?recurse cs)
  HCase t x b cs     -> hcase (eval t) (evalClosureLazy x b) (EC ?sub ?env ?recurse cs)
  Split x b cs       -> VLam $ NCl x $ CSplit (evalClosureLazy x b) (EC ?sub ?env ?recurse cs)
  HSplit x b cs      -> VLam $ NCl x $ CHSplit (evalClosureLazy x b) (EC ?sub ?env ?recurse cs)
  HTyCon i ts        -> VHTyCon i (params ts)
  HDCon i ps fs s    -> hdcon i (lazyParams ps) (spine fs) (sub s)

  -- Pi
  Pi x a b           -> VPi (eval a) (evalClosure x b)
  App t u            -> eval t ∙ eval u
  Lam x t            -> VLam (evalClosure x t)

  -- Sigma
  Sg x a b           -> VSg (eval a) (evalClosure x b)
  Pair x t u         -> VPair x (eval t) (eval u)
  Proj1 t x          -> proj1 x (eval t)
  Proj2 t x          -> proj2 x (eval t)

  -- Wrap
  Wrap x a           -> VWrap x (eval a)
  Pack x t           -> VPack x (eval t)
  Unpack t x         -> unpack x (eval t)

  -- U
  U                  -> VU

  -- Path
  Path x a t u       -> VPath (evalIClosure x a) (eval t) (eval u)
  PApp l r t i       -> papp (eval l) (eval r) (eval t) (evalI i)
  PLam l r x t       -> VPLam (eval l) (eval r) (evalIClosure x t)

  -- Kan
  Coe r r' x a t     -> coe   (evalI r) (evalI r') (bindIS x \_ -> eval a) (eval t)
  HCom r r' a t b    -> hcomSC (evalI r) (evalI r') (eval a) (evalSysHComSC t) (eval b)

  -- Glue
  GlueTy a sys       -> glueTy (eval a) (evalSys sys)
  Glue t eqs sys     -> glue   (eval t) (evalSys eqs) (evalSys sys)
  Unglue t sys       -> unglue (eval t) (evalSys sys)

  -- Line
  Line x a           -> VLine (evalIClosure x a)
  LApp t i           -> lapp (eval t) (evalI i)
  LLam x t           -> VLLam (evalIClosure x t)

  -- Misc
  WkI t              -> wkIS (eval t)
  Hole h             -> VHole h

  -- Builtins
  Refl t             -> refl (eval t)
  Sym a x y p        -> sym (eval a) (eval x) (eval y) (eval p)
  Trans a x y z p q  -> trans (eval a) (eval x) (eval y) (eval z) (eval p) (eval q)
  Ap f x y p         -> ap_ (eval f) (eval x) (eval y) (eval p)
  Com r r' i a t b   -> comSC (evalI r) (evalI r') (bindIS i \_ -> eval a) (evalSysHComSC t) (eval b)


----------------------------------------------------------------------------------------------------
-- Forcing
----------------------------------------------------------------------------------------------------

class Force a b | a -> b where
  frc  :: NCofArg => DomArg => a -> b           -- force a value wrt current cof. Idempotent when
                                                -- the type is (a -> a).
  frcS :: SubArg => NCofArg => DomArg => a -> b -- apply a substitution and then force. It's always
                                                -- an *error* to apply it multiple times.

-- | Force all cofs, subs *and* unfoldings away.
frcFull :: NCofArg => DomArg => Val -> Val
frcFull v = case frc v of
  VUnf _ _ v' -> frcFull v'
  v           -> v

instance Force I I where
  frc  i = appNCof ?cof i; {-# inline frc #-}
  frcS i = appNCof ?cof (sub i); {-# inline frcS #-}

instance Force Sub Sub where
  frc  s = appNCofToSub ?cof s; {-# inline frc #-}
  frcS s = appNCofToSub ?cof (sub s); {-# inline frcS #-}

instance Force NeCof VCof where
  frc  (NCEq i j) = eq i j
  frcS (NCEq i j) = eqS i j

instance Force Res Val where
  frc  (Res v True) = frc v
  frc  (Res v _   ) = v
  frcS (Res v True) = frcS v
  frcS (Res v _   ) = v
  {-# inline frc  #-}
  {-# inline frcS #-}

instance Force Val Val where
  frc = \case
    VSub v s           -> let ?sub = wkSub s in frcS v
    v@VUnf{}           -> v
    VNe t              -> frc t
    VGlueTy a sys      -> frc (glueTy' a (frc sys))
    VHDCon i ps fs s   -> frc (hdcon' i ps fs s)
    VHCom r r' a sys t -> frc (hcom' r r' a (frc sys) t)
    VGlue t eqs sys    -> frc (glue' t (frc eqs) (frc sys))
    v                  -> v

  frcS = \case
    VSub v s           -> let ?sub = sub s in frcS v
    VUnf inf v v'      -> VUnf inf (sub v) (sub v')
    VNe t              -> frcS t
    VGlueTy a sys      -> frc (glueTy' (sub a) (frcS sys))
    VHDCon i ps fs s   -> frc (hdcon' i (sub ps) (sub fs) (sub s))
    VHCom r r' a sys t -> frc (hcom' (sub r) (sub r') (sub a) (frcS sys) (sub t))
    VGlue t eqs sys    -> frc (glue' (sub t) (frcS eqs) (frcS sys))

    VPi a b            -> VPi (sub a) (sub b)
    VLam t             -> VLam (sub t)
    VPath a t u        -> VPath (sub a) (sub t) (sub u)
    VPLam l r t        -> VPLam (sub l) (sub r) (sub t)
    VSg a b            -> VSg (sub a) (sub b)
    VPair x t u        -> VPair x (sub t) (sub u)
    VWrap x t          -> VWrap x (sub t)
    VPack x t          -> VPack x (sub t)
    VU                 -> VU
    VHole h            -> VHole h
    VLine t            -> VLine (sub t)
    VLLam t            -> VLLam (sub t)
    VTyCon x ts        -> VTyCon x (sub ts)
    VDCon ci sp        -> VDCon ci (sub sp)
    VHTyCon i ps       -> VHTyCon i (sub ps)
  {-# noinline frcS #-}

instance Force Ne Val where
  frc = \case
    t@NLocalVar{}      -> VNe t
    t@NDontRecurse{}   -> VNe t
    NSub n s           -> let ?sub = wkSub s in frcS n
    NApp t u           -> frc (app' (frc t) u)
    NPApp l r t i      -> frc (papp' l r (frc t) i)
    NProj1 t x         -> frc (proj1' x (frc t))
    NProj2 t x         -> frc (proj2' x (frc t))
    NUnpack t x        -> frc (unpack' x (frc t))
    NCoe r r' a t      -> frc (coe' r r' (frc a) (frc t))
    NUnglue t sys      -> frc (unglue' (frc t) (frc sys))
    NLApp t i          -> frc (lapp' (frc t) i)
    NCase t b cs       -> frc (case_' (frc t) b cs)
    NHCase t b cs      -> frc (hcase' (frc t) b cs)
  {-# noinline frc #-}

  frcS = \case
    t@NLocalVar{}      -> VNe t
    t@NDontRecurse{}   -> VNe t
    NSub n s           -> let ?sub = sub s in frcS n
    NApp t u           -> frc (app' (frcS t) (sub u))
    NPApp l r t i      -> frc (papp' (sub l) (sub r) (frcS t) (frcS i))
    NProj1 t x         -> frc (proj1' x (frcS t))
    NProj2 t x         -> frc (proj2' x (frcS t))
    NUnpack t x        -> frc (unpack' x (frcS t))
    NCoe r r' a t      -> frc (coe' (frcS r) (frcS r') (frcS a) (frcS t))
    NUnglue t sys      -> frc (unglue' (frcS t) (frcS sys))
    NLApp t i          -> frc (lapp' (frcS t) (frcS i))
    NCase t b cs       -> frc (case_' (frcS t) (sub b) (sub cs))
    NHCase t b cs      -> frc (hcase' (frcS t) (sub b) (sub cs))
  {-# noinline frcS #-}

instance Force NeSys VSys where

  -- NOTE: it could also be a sensible choice to not force component bodies!
  -- The forcing here is lazy, so we get a thunk accummulation if we do it
  -- repeatedly. We get thunk accummulation if we force, we get potential
  -- computation duplication if we don't. Neither looks very bad.
  frc = \case
    NSEmpty      -> vsempty
    NSCons t sys -> vscons (frc (t^.binds)) (frc (t^.body)) (frc sys)

  frcS = \case
    NSEmpty      -> vsempty
    NSCons t sys -> vscons (frcS (t^.binds)) (frcS (t^.body)) (frcS sys)

instance Force NeSysHCom VSysHCom where
  -- Definitions are more unrolled and optimized here. The semantic vshcons
  -- operations always rename the bound vars to the current fresh var. The
  -- optimized "frc" here avoids substitution.

  frc = \case
    NSHEmpty ->
      vshempty
    NSHCons t sys -> case frc (t^.binds) of
      VCTrue   -> VSHTotal (t^.body)
      VCFalse  -> frc sys
      VCNe cof -> case frc sys of
        VSHTotal v' -> VSHTotal v'
        VSHNe sys   -> VSHNe (NSHCons (bindCof cof (t^.body)) sys)

  frcS = \case
    NSHEmpty ->
      vshempty
    NSHCons t sys -> case frcS (t^.binds) of
      VCTrue   -> VSHTotal (frcS (t^.body))
      VCFalse  -> frcS sys
      VCNe cof -> case frcS sys of
        VSHTotal v' -> VSHTotal v'
        VSHNe sys   -> VSHNe (NSHCons (bindCof cof (frcS (t^.body))) sys)

instance Force a fa => Force (BindI a) (BindI fa) where
  frc (BindI x i a) =
    let ?cof = lift (setDom i ?cof) in
    seq ?cof (BindI x i (frc a))
  {-# inline frc #-}

  frcS (BindI x i a) =
    let fresh = dom ?cof in
    let ?cof  = lift ?cof in
    let ?sub  = lift (setCod i ?sub) in
    seq ?sub $ seq ?cof $ BindI x fresh (frcS a)
  {-# inline frcS #-}

instance Force a fa => Force (BindILazy a) (BindILazy fa) where

  frc (BindILazy x i a) =
    let ?cof = lift (setDom i ?cof) in
    seq ?cof (BindILazy x i (frc a))
  {-# inline frc #-}

  frcS (BindILazy x i a) =
    let fresh = dom ?cof in
    let ?cof  = lift ?cof in
    let ?sub  = lift (setCod i ?sub) in
    seq ?sub $ seq ?cof $ BindILazy x fresh (frcS a)
  {-# inline frcS #-}

----------------------------------------------------------------------------------------------------
-- Pushing neutral & frozen substitutions
----------------------------------------------------------------------------------------------------

unSubNe :: Ne -> Ne
unSubNe = \case
  NSub n s -> let ?sub = s in unSubNeS n
  n        -> n

unSubNeS :: SubArg => Ne -> Ne
unSubNeS = \case
  NSub n s           -> let ?sub = sub s in unSubNeS n
  NLocalVar x        -> NLocalVar x
  NDontRecurse x     -> NDontRecurse x
  NApp t u           -> NApp (sub t) (sub u)
  NPApp l r p i      -> NPApp (sub l) (sub r) (sub p) (sub i)
  NProj1 t x         -> NProj1 (sub t) x
  NProj2 t x         -> NProj2 (sub t) x
  NUnpack t x        -> NUnpack (sub t) x
  NCoe r r' a t      -> NCoe (sub r) (sub r') (sub a) (sub t)
  NUnglue a sys      -> NUnglue (sub a) (sub sys)
  NLApp t i          -> NLApp (sub t) (sub i)
  NCase t b cs       -> NCase (sub t) (sub b) (sub cs)
  NHCase t b cs      -> NHCase (sub t) (sub b) (sub cs)

unSubFrozen :: Frozen -> Frozen
unSubFrozen = \case
  FSub n s -> let ?sub = s in unSubFrozenS n
  n        -> n

unSubFrozenS :: SubArg => Frozen -> Frozen
unSubFrozenS = \case
  f@FTopVar{}           -> f
  FSub f s              -> let ?sub = sub s in unSubFrozenS f
  FApp t u              -> FApp (sub t) (sub u)
  FPApp l r t i         -> FPApp (sub l) (sub r) (sub t) (sub i)
  FLApp l i             -> FLApp (sub l) (sub i)
  FProj1 x t            -> FProj1 x (sub t)
  FProj2 x t            -> FProj2 x (sub t)
  FUnpack t x           -> FUnpack (sub t) x
  FCoeTy r r' a t       -> FCoeTy (sub r) (sub r') (sub a) (sub t)
  FCoeVal r r' a t      -> FCoeVal (sub r) (sub r') (sub a) (sub t)
  FHComTy r r' a sys t  -> FHComTy (sub r) (sub r') (sub a) (sub sys) (sub t)
  FHComVal r r' a sys t -> FHComVal (sub r) (sub r') (sub a) (sub sys) (sub t)
  FUnglue t sys         -> FUnglue (sub t) (sub sys)
  FCase_ t ncs cs       -> FCase_ (sub t) (sub ncs) (sub cs)
  FHCase_ t ncs cs      -> FHCase_ (sub t) (sub ncs) (sub cs)

----------------------------------------------------------------------------------------------------
-- Definitions
----------------------------------------------------------------------------------------------------

fun :: Val -> Val -> Val
fun a b = VPi a $ NCl N_ $ CConst b

funf :: Val -> Val -> Val
funf a b = VPi a $ NCl N_ $ CConst b

-- | (A : U) -> A -> A -> U
path :: Val -> Val -> Val -> Val
path a t u = VPath (NICl N_ (ICConst a)) t u

-- | (x : A) -> PathP _ x x
refl :: Val -> Val
refl ~t = VPLam t t $ NICl N_ $ ICConst t

-- | sym (A : U)(x y : A) (p : x = y) : y = x
--     := λ i. hcom 0 1 A [i=0 j. p j; i=1 j. x] x;
sym :: Val -> Val -> Val -> Val -> Val
sym a ~x ~y p = VPLam y x $ NICl i_ (ICSym a x y p)

-- | trans (A : U)(x y z : A) (p : x = y) (q : y = z) : x = z
--    := λ i. hcom 0 1 A [i=0 j. x; i=1 j. q j] (p i);
trans :: Val -> Val -> Val -> Val -> Val -> Val -> Val
trans a ~x ~y ~z p q = VPLam x z $ NICl i_ $ ICTrans a x y z p q

-- | ap (A B : U)(f : A -> B)(x y : A)(p : x = y) : f x = f y
--     := λ i. f (p i)
ap_ :: NCofArg => DomArg => Val -> Val -> Val -> Val -> Val
ap_ f ~x ~y p = let ~ff = frc f in
                VPLam (ff ∙ x) (ff ∙ y) $ NICl i_ $ ICAp ff x y p

-- | (A : U)(B : U) -> (A -> B) -> U
isEquiv :: Val -> Val -> Val -> Val
isEquiv a b f = VSg (fun b a) $ NCl g_ $ CIsEquiv1 a b f

-- | U -> U -> U
equiv :: Val -> Val -> Val
equiv a b = VSg (fun a b) $ NCl f_ $ CEquiv a b

-- | U -> U
equivInto :: Val -> Val
equivInto a = VSg VU $ NCl ty_ $ CEquivInto a

-- | idIsEquiv : (A : U) -> isEquiv (\(x:A).x)
idIsEquiv :: Val -> Val
idIsEquiv a =
  VPair g_    (VLam $ NCl a_ C'λ'a''a)     $
  VPair linv_ (VLam $ NCl a_ C'λ'a'i''a)   $
  VPair rinv_ (VLam $ NCl b_ C'λ'a'i''a)   $
  VPack coh_  (VLam $ NCl a_ C'λ'a'i'j''a)

-- | Identity function packed together with isEquiv.
theIdEquiv :: Val -> Val
theIdEquiv a = VPair f_ (VLam $ NCl x_ C'λ'a''a) (idIsEquiv a)


-- Coercion is an equivalence
----------------------------------------------------------------------------------------------------

{-
  coeIsEquiv : (A : I → U) (r r' : I) → isEquiv (λ x. coe r r' A x)
  coeIsEquiv A r r' =

    ffill i x      := coe r i A x
    gfill i x      := coe i r A x
    linvfill i x j := hcom r i (A r) [j=0 k. coe k r A (coe r k A x); j=1 k. x] x
    rinvfill i x j := hcom i r (A i) [j=0 k. coe k i A (coe i k A x); j=1 k. x] x

    g    := λ x^0. gfill r' x
    linv := λ x^0 j^1. linvfill r' x j
    rinv := λ x^0 j^1. rinvfill r' x j
    coh  := λ x^0 l^1 k^2. com r r' A [k=0 i. ffill i (linvfill i x l)
                                      ;k=1 i. ffill i x
                                      ;l=0 i. rinvfill i (ffill i x) k]
                                      ;l=1 i. ffill i x
                                      x
-}

ffill :: NCofArg => DomArg => BindI Val -> I -> I -> Val -> Val
ffill a r i x = coe r i a x; {-# inline ffill #-}

gfill :: NCofArg => DomArg => BindI Val -> I -> I -> Val -> Val
gfill a r i x = coe i r a x; {-# inline gfill #-}

linvfill :: NCofArg => DomArg => BindI Val -> I -> I -> Val -> I -> Val
linvfill a r i x j =
  hcom r i (a ∙ r)
    (vshcons (eq j I0) k_ (\k -> coe k r a (coe r k a x)) $
     vshcons (eq j I1) k_ (\_ -> x) $
     vshempty)
    x

rinvfill :: NCofArg => DomArg => BindI Val -> I -> I -> Val -> I -> Val
rinvfill a r i x j =
  hcom i r (a ∙ i)
    (vshcons (eq j I0) k_ (\k -> coe k i a (coe i k a x)) $
     vshcons (eq j I1) k_ (\_ -> x) $
     vshempty)
    x

coeCoherence :: NCofArg => DomArg => BindI Val -> I -> I -> Val -> I -> I -> Val
coeCoherence a r r' x l k =
  hcom r r' (a ∙ r')
    (vshcons (eq k I0) i_ (\i -> coe i r' a (ffill a r i (linvfill a r i x l))) $
     vshcons (eq k I1) i_ (\i -> coe i r' a (ffill a r i x)) $
     vshcons (eq l I0) i_ (\i -> coe i r' a (rinvfill a r i (ffill a r i x) k)) $
     vshcons (eq l I1) i_ (\i -> coe i r' a (ffill a r i x)) $
     vshempty)
    (coe r r' a x)

coeIsEquiv :: BindI Val -> I -> I -> Val
coeIsEquiv a r r' =
  VPair g_    (VLam $ NCl x_ $ CCoeAlong a r' r) $
  VPair linv_ (VLam $ NCl x_ $ CCoeLinv0 a r r') $
  VPair rinv_ (VLam $ NCl x_ $ CCoeRinv0 a r r') $
  VPack coh_  (VLam $ NCl x_ $ CCoeCoh0  a r r')

-- | Coercion function packed together with isEquiv.
theCoeEquiv :: BindI Val -> I -> I -> Val
theCoeEquiv a r r' = VPair f_ (VLam $ NCl x_ $ CCoeAlong a r r') (coeIsEquiv a r r')
