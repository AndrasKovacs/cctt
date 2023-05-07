
module Core where

import Common
import CoreTypes
import Interval

----------------------------------------------------------------------------------------------------
{-
FORCING
  - moving under cofibrations:
    - We lose off-diagonals
    - We lose system forcing
  - semantic system cons-es always take forced cofibrations

TODO:
  - propagate VHole from strict system projection

-}

type EvalArgs a = SubArg => NCofArg => DomArg => EnvArg => RecurseArg => a

----------------------------------------------------------------------------------------------------
-- Context manipulation primitives
----------------------------------------------------------------------------------------------------

-- | Get a fresh ivar when not working under a Sub.
freshIVar :: (NCofArg => IVar -> a) -> (NCofArg => a)
freshIVar act =
  let fresh = dom ?cof in
  if  fresh == maxIVar then error "RAN OUT OF IVARS IN EVAL" else
  let ?cof  = setDom (fresh+1) ?cof `ext` IVar fresh in
  seq ?cof (act fresh)
{-# inline freshIVar #-}

freshI :: (NCofArg => I -> a) -> (NCofArg => a)
freshI act = freshIVar \i -> act (IVar i)
{-# inline freshI #-}

-- | Get a fresh ivar, when working under a Sub.
freshIVarS :: (SubArg => NCofArg => IVar -> a) -> (SubArg => NCofArg => a)
freshIVarS act =
  let fresh = dom ?cof in
  let ?sub  = setDom (fresh+1) ?sub `ext` IVar fresh in
  let ?cof  = setDom (fresh+1) ?cof `ext` IVar fresh in
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
assumeCof cof act = let ?cof = conjNeCof ?cof cof in act
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

bindIUnLazy :: BindILazy a -> BindI a
bindIUnLazy (BindILazy x i a) = BindI x i a
{-# inline bindIUnLazy #-}

----------------------------------------------------------------------------------------------------
-- Cof and Sys semantics
----------------------------------------------------------------------------------------------------

conjIVarI :: NCof -> IVar -> I -> NCof
conjIVarI cof x i = mapSub id go cof where
  go _ j = matchIVarF j (\y -> if x == y then i else j) j

conjNeCof :: NCof -> NeCof -> NCof
conjNeCof ncof necof = case necof of
  NCAnd c1 c2 -> ncof `conjNeCof` c1 `conjNeCof` c2
  NCEq i j    -> case (i, j) of
    (IVar x, IVar y) -> let (!x', !i') = if x > y then (x, IVar y)
                                                  else (y, IVar x) in
                        conjIVarI ncof x' i'
    (IVar x, j     ) -> conjIVarI ncof x j
    (i     , IVar y) -> conjIVarI ncof y i
    (i     , j     ) -> impossible

vcne :: NCofArg => NeCof -> IVarSet -> VCof
vcne nc is = VCNe (NeCof' (conjNeCof ?cof nc) nc) is
{-# inline vcne #-}

ceq :: NCofArg => I -> I -> VCof
ceq c1 c2 = case (doSub ?cof c1, doSub ?cof c2) of
  (i, j) | i == j -> VCTrue
  (i, j) -> matchIVar i
    (\x -> matchIVar j
      (\y -> vcne (NCEq i j) (insertIVarF x $ insertIVarF y mempty))
      (vcne (NCEq i j) (insertIVarF x mempty)))
    (matchIVar j
      (\y -> vcne (NCEq i j) (insertIVarF y mempty))
     VCFalse)

evalI :: SubArg => NCofArg => I -> I
evalI i = doSub ?cof (doSub ?sub i)
{-# inline evalI #-}

evalCofEq :: SubArg => NCofArg => CofEq -> VCof
evalCofEq (CofEq i j) = ceq (doSub ?sub i) (doSub ?sub j)
{-# inline evalCofEq #-}

evalCof :: SubArg => NCofArg => Cof -> VCof
evalCof = \case
  CTrue       -> VCTrue
  CAnd eq cof -> case evalCofEq eq of
    VCTrue      -> evalCof cof
    VCFalse     -> VCFalse
    VCNe c is -> let ?cof = c^.extended in case evalCof cof of
      VCTrue      -> VCNe c is
      VCFalse     -> VCFalse
      VCNe c' is' -> VCNe (NeCof' (c^.extended) (NCAnd (c^.extra) (c'^.extra)))
                          (is <> is')

vsempty :: VSys
vsempty = VSNe (WIS NSEmpty mempty)

vscons :: NCofArg => VCof -> (NCofArg => Val) -> VSys -> VSys
vscons cof v ~sys = case cof of
  VCTrue      -> VSTotal v
  VCFalse     -> sys
  VCNe cof is -> case sys of
    VSTotal v'         -> VSTotal v'
    VSNe (WIS sys is') -> VSNe (WIS (NSCons (bindCofLazy cof v) sys) (is <> is'))
{-# inline vscons #-}

-- | Extend a *neutral* system with a *non-true* cof.
nscons :: NCofArg => VCof -> (NCofArg => Val) -> NeSys -> NeSys
nscons cof v ~sys = case cof of
  VCTrue     -> impossible
  VCFalse    -> sys
  VCNe cof _ -> NSCons (bindCofLazy cof v) sys
{-# inline nscons #-}

evalSys :: EvalArgs (Sys -> VSys)
evalSys = \case
  SEmpty          -> vsempty
  SCons cof t sys -> vscons (evalCof cof) (eval t) (evalSys sys)

vshempty :: VSysHCom
vshempty = VSHNe (WIS NSHEmpty mempty)

vshcons :: NCofArg => VCof -> Name -> (NCofArg => I -> Val) -> VSysHCom -> VSysHCom
vshcons cof i v ~sys = case cof of
  VCTrue      -> VSHTotal (bindILazy i v)
  VCFalse     -> sys
  VCNe cof is -> case sys of
    VSHTotal v'         -> VSHTotal v'
    VSHNe (WIS sys is') -> VSHNe (WIS (NSHCons (bindCof cof (bindILazy i v)) sys) (is <> is'))
{-# inline vshcons #-}

vshconsS :: SubArg => NCofArg => VCof -> Name -> (SubArg => NCofArg => I -> Val) -> VSysHCom -> VSysHCom
vshconsS cof i v ~sys = case cof of
  VCTrue      -> VSHTotal (bindILazyS i v)
  VCFalse     -> sys
  VCNe cof is -> case sys of
    VSHTotal v'         -> VSHTotal v'
    VSHNe (WIS sys is') -> VSHNe $ WIS (NSHCons (bindCof cof (bindILazyS i v)) sys) (is <> is')
{-# inline vshconsS #-}

evalSysHCom :: EvalArgs (SysHCom -> VSysHCom)
evalSysHCom = \case
  SHEmpty            -> vshempty
  SHCons cof x t sys -> vshconsS (evalCof cof) x (\_ -> eval t) (evalSysHCom sys)

occursInNeCof :: NeCof -> IVar -> Bool
occursInNeCof cof i' = case cof of
  NCEq i j    -> i == IVar i' || j == IVar i'
  NCAnd c1 c2 -> occursInNeCof c1 i' || occursInNeCof c2 i'

neCofVars :: NeCof -> IVarSet
neCofVars = \case
  NCEq i j    -> insertIF i $ insertIF j mempty
  NCAnd c1 c2 -> neCofVars c1 <> neCofVars c2


-- Alternative hcom and com semantics which shortcuts to term instantiation if
-- the system is total. We make use of the knowledge that the system argument
-- comes from the syntax.
----------------------------------------------------------------------------------------------------

data VSysHCom' = VSHTotal' Name Tm | VSHNe' NeSysHCom IVarSet deriving Show

vshempty' :: VSysHCom'
vshempty' = VSHNe' NSHEmpty mempty

vshconsS' :: EvalArgs (VCof -> Name -> Tm -> VSysHCom' -> VSysHCom')
vshconsS' cof i t ~sys = case cof of
  VCTrue      -> VSHTotal' i t
  VCFalse     -> sys
  VCNe cof is -> case sys of
    VSHTotal' x t  -> VSHTotal' x t
    VSHNe' sys is' -> VSHNe' (NSHCons (bindCof cof (bindILazyS i \_ -> eval t)) sys)
                             (is <> is')
{-# inline vshconsS' #-}

evalSysHCom' :: EvalArgs (SysHCom -> VSysHCom')
evalSysHCom' = \case
  SHEmpty            -> vshempty'
  SHCons cof x t sys -> vshconsS' (evalCof cof) x t (evalSysHCom' sys)

hcom' :: EvalArgs (I -> I -> Val -> VSysHCom' -> Val -> Val)
hcom' r r' ~a ~t ~b
  | r == r'             = b
  | VSHTotal' x t  <- t = let ?sub = ?sub `ext` r' in eval t
  | VSHNe' nsys is <- t = hcomdn r r' a (WIS nsys is) b
{-# inline hcom' #-}

com' :: EvalArgs (I -> I -> BindI Val -> VSysHCom' -> Val -> Val)
com' r r' ~a ~sys ~b
  | r == r'               = b
  | VSHTotal' x t  <- sys = let ?sub = ?sub `ext` r' in eval t
  | VSHNe' nsys is <- sys = hcomdn r r' (a ∙ r')
                              (mapNeSysHCom' (\i t -> coe i r' a (t ∙ i)) (WIS nsys is))
                              (coed r r' a b)
{-# inline com' #-}

----------------------------------------------------------------------------------------------------
-- Mapping
----------------------------------------------------------------------------------------------------

unBindCof :: NCofArg => BindCof a -> NeCof'
unBindCof t = NeCof' (conjNeCof ?cof (t^.binds)) (t^.binds)

unBindCofLazy :: NCofArg => BindCofLazy a -> NeCof'
unBindCofLazy t = NeCof' (conjNeCof ?cof (t^.binds)) (t^.binds)

mapBindCof :: NCofArg => BindCof a -> (NCofArg => a -> b) -> BindCof b
mapBindCof t f = bindCof (unBindCof t) (f (t^.body))
{-# inline mapBindCof #-}

mapBindCofLazy :: NCofArg => BindCofLazy a -> (NCofArg => a -> b) -> BindCofLazy b
mapBindCofLazy t f = bindCofLazy (unBindCofLazy t) (f (t^.body))
{-# inline mapBindCofLazy #-}

bindIFromLazy :: BindILazy a -> BindI a
bindIFromLazy (BindILazy x i a) = BindI x i a; {-# inline bindIFromLazy #-}

bindIToLazy :: BindILazy a -> BindI a
bindIToLazy (BindILazy x i z) = BindI x i z; {-# inline bindIToLazy #-}

mapBindI :: SubAction a => NCofArg => BindI a -> (NCofArg => I -> a -> b) -> BindI b
mapBindI t f = bindI (t^.name) (\i -> f i (t ∙ i))
{-# inline mapBindI #-}

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
  let ?cof = setDomCod (i + 1) i ?cof `ext` IVar i in
  seq ?cof (BindILazy x i (f (IVar i) a))
{-# inline umapBindILazy #-}

umapBindI :: NCofArg => BindI a -> (NCofArg => I -> a -> b) -> BindI b
umapBindI (BindI x i a) f =
  let ?cof = setDomCod (i + 1) i ?cof `ext` IVar i in
  seq ?cof (BindI x i (f (IVar i) a))
{-# inline umapBindI #-}

proj1BindIFromLazy :: NCofArg => DomArg => Name -> BindILazy Val -> BindI Val
proj1BindIFromLazy x t = umapBindI (bindIToLazy t) (\_ -> proj1 x)
{-# inline proj1BindIFromLazy #-}

mapNeSys :: NCofArg => (NCofArg => Val -> Val) -> NeSys -> NeSys
mapNeSys f sys = go sys where
  go = \case
    NSEmpty      -> NSEmpty
    NSCons t sys -> NSCons (mapBindCofLazy t f) (go sys)
{-# inline mapNeSys #-}

mapNeSys' :: NCofArg => (NCofArg => Val -> Val) -> NeSys' -> NeSys'
mapNeSys' f sys = sys & body %~ mapNeSys f
{-# inline mapNeSys' #-}

mapNeSysHCom :: NCofArg => (NCofArg => I -> BindILazy Val -> Val) -> NeSysHCom -> NeSysHCom
mapNeSysHCom f sys = go sys where
  go = \case
    NSHEmpty      -> NSHEmpty
    NSHCons t sys -> NSHCons (mapBindCof t \t -> bindILazy (t^.name) (\i -> f i t)) (go sys)
{-# inline mapNeSysHCom #-}

mapNeSysHCom' :: NCofArg => (NCofArg => I -> BindILazy Val -> Val) -> NeSysHCom' -> NeSysHCom'
mapNeSysHCom' f sys = sys & body %~ mapNeSysHCom f
{-# inline mapNeSysHCom' #-}

mapVSysHCom :: NCofArg => (NCofArg => I -> BindILazy Val -> Val) -> VSysHCom -> VSysHCom
mapVSysHCom f sys = case sys of
  VSHTotal v         -> VSHTotal (bindILazy (v^.name) \i -> f i v)
  VSHNe (WIS sys is) -> VSHNe (WIS (mapNeSysHCom f sys) is)
{-# inline mapVSysHCom #-}

mapNeSysToH :: NCofArg => (NCofArg => I -> Val -> Val) -> NeSys -> NeSysHCom
mapNeSysToH f sys = case sys of
  NSEmpty      -> NSHEmpty
  NSCons t sys -> NSHCons (bindCof (unBindCofLazy t) (bindILazy "i" \i -> f i (t^.body)))
                          (mapNeSysToH f sys)
{-# inline mapNeSysToH #-}

mapNeSysToH' :: NCofArg => (NCofArg => I -> Val -> Val) -> NeSys' -> NeSysHCom'
mapNeSysToH' f (WIS sys is) = WIS (mapNeSysToH f sys) is
{-# inline mapNeSysToH' #-}

mapNeSysFromH :: NCofArg => (NCofArg => BindILazy Val -> Val) -> NeSysHCom -> NeSys
mapNeSysFromH f sys = case sys of
  NSHEmpty      -> NSEmpty
  NSHCons t sys -> NSCons (bindCofLazy (unBindCof t) (f (t^.body))) (mapNeSysFromH f sys)
{-# inline mapNeSysFromH #-}

-- | Filter out the components of system which depend on a binder, and at the same time
--   push the binder inside so that we get a NeSysHCom'.
forallNeSys :: BindI NeSys -> NeSysHCom'
forallNeSys (BindI x i sys) = case sys of
  NSEmpty -> WIS NSHEmpty mempty
  NSCons t sys ->
    if occursInNeCof (t^.binds) i
      then forallNeSys (BindI x i sys)
      else case forallNeSys (BindI x i sys) of
        WIS sys is ->
          WIS
          (NSHCons
            (BindCof (t^.binds) (BindILazy x i (t^.body)))
            sys)
          (is <> neCofVars (t^.binds))

-- System concatenation
----------------------------------------------------------------------------------------------------

catNeSysHCom' :: NeSysHCom' -> NeSysHCom' -> NeSysHCom'
catNeSysHCom' (WIS sys is) (WIS sys' is') = WIS (catNeSysHCom sys sys') (is <> is')
{-# inline catNeSysHCom' #-}

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

instance Apply Val Val Val NCofArg DomArg where
  (∙) t u = case frc t of
    VLam t    -> t ∙ u
    VNe t is  -> VNe (NApp t u) is
    v@VHole{} -> v
    _         -> impossible
  {-# inline (∙) #-}

instance Apply (BindI a) I a (SubAction a) NCofArg where
  (∙) (BindI x i a) j | IVar i == j = a
  (∙) (BindI x i a) j =
    let s = setCod i (idSub (dom ?cof)) `ext` j
    in doSub s a
  {-# inline (∙) #-}

instance Apply (BindILazy a) I a (SubAction a) NCofArg where
  (∙) (BindILazy x i a) j | IVar i == j = a
  (∙) (BindILazy x i a) j =
    let s = setCod i (idSub (dom ?cof)) `ext` j
    in doSub s a
  {-# inline (∙) #-}

instance Apply NamedIClosure I Val NCofArg DomArg where
  (∙) = icapp; {-# inline (∙) #-}

infixl 8 ∙~
(∙~) :: NCofArg => DomArg => Val -> Val -> Val
(∙~) t ~u = case frc t of
  VLam t    -> t ∙ u
  VNe t is  -> VNe (NApp t u) is
  v@VHole{} -> v
  _         -> impossible
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
  CEval (EC s env rc t) -> let ?env = EDef env u; ?sub = wkSub s; ?recurse = rc in eval t
  CSplit b tag ecs      -> case_ u b tag ecs
  CHSplit b tag ecs     -> hcase u b tag ecs

  CCoePi r r' a b t ->
    let ~x = u in
    coe r r' (bindI "j" \j -> b ∙ j ∙ coe r' j a x) (t ∙ coe r' r a x)

  CHComPi r r' a b sys base ->
    hcom r r'
      (b ∙ u)
      (mapVSysHCom (\i t -> t ∙ i ∙ u) (frc sys))
      (base ∙ u)

  CConst v -> v

  -- isEquiv : (A → B) → U
  -- isEquiv A B f :=
  --     (g^1    : B → A)
  --   × (linv^2 : (x^4 : A) → Path A x (g (f x)))
  --   × (rinv^3 : (x^5 : B) → Path B (f (g x)) x)
  --   × (coh    : (x^6 : A) →
  --             PathP (i^7) (Path B (f (linv x {x}{g (f x)} i)) (f x))
  --                   (refl B (f x))
  --                   (rinv (f x)))

  CIsEquiv1 a b f -> let ~g = u in
    VSg (VPi a $ NCl "x" $ CIsEquiv4 a f g) $ NCl "linv" $ CIsEquiv2 a b f g

  CIsEquiv2 a b f g -> let ~linv = u in
    VSg (VPi b $ NCl "x" $ CIsEquiv5 b f g) $ NCl "rinv" $ CIsEquiv3 a b f g linv

  CIsEquiv3 a b f g linv -> let ~rinv = u in
    VWrap "coh" (VPi a $ NCl "a" $ CIsEquiv6 b f g linv rinv)

  CIsEquiv4 a f g -> let ~x = u in path a x (g ∙ (f ∙ x))
  CIsEquiv5 b f g -> let ~x = u in path b (f ∙ (g ∙ x)) x

  CIsEquiv6 b f g linv rinv ->
    let ~x  = u
        ~fx = f ∙ x in
    VPath (NICl "i" $ ICIsEquiv7 b f g linv x) (refl fx) (rinv ∙ fx)

  -- equiv A B = (f* : A -> B) × isEquiv a b f
  CEquiv a b -> let ~f = u in isEquiv a b f

  -- [A]  (B* : U) × equiv B A
  CEquivInto a -> let ~b = u in equiv b a

  -- ------------------------------------------------------------

  C'λ'a''a     -> u
  C'λ'a'i''a   -> refl u
  C'λ'a'i'j''a -> let ru = refl u in VPLam ru ru $ NICl "i" $ ICConst ru

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
                                      ;l=0 i. ffill i x
                                      ;l=1 i. rinvfill i (ffill i x) k]
                                      x
-}

  CCoeAlong a r r' ->
    let ~x = u in coe r r' a x

  CCoeLinv0 a r r' ->
    let ~x   = u
        -- x = g (f x)
        ~lhs = x
        ~rhs = coe r' r a (coe r r' a x)
    in VPLam lhs rhs $ NICl "j" $ ICCoeLinv1 a r r' x

  CCoeRinv0 a r r' ->
    let ~x   = u
        -- f (g x) = x
        ~lhs = coe r r' a (coe r' r a x)
        ~rhs = x
    in VPLam lhs rhs $ NICl "j" $ ICCoeRinv1 a r r' x

  CCoeCoh0 a r r' ->
    let ~x = u

        -- (λ k. coe r r' a x)
        ~lhs = refl (coe r r' a x)

        -- (λ k. rinvfill a r r' (ffill a r r' x) k)
        ~rhs =
           -- coe r r' a (coe r' r a (coe r r' a x))
           let ~lhs' = coe r r' a (coe r' r a (coe r r' a x))
               ~rhs' = coe r r' a x in

           VPLam lhs' rhs' $ NICl "k" $ ICCoeCoh0Rhs a r r' x

    in VPLam lhs rhs $ NICl "l" $ ICCoeCoh1 a r r' x

  -- CHInd motive ms t ->
  --   elim motive ms (t ∙ u)


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
      (vshcons (ceq j I0) "i" (\i -> coe i r' (bindI "i" \i -> a ∙ i ∙ j) (lhs ∙ i)) $
       vshcons (ceq j I1) "i" (\i -> coe i r' (bindI "i" \i -> a ∙ i ∙ j) (rhs ∙ i)) $
       vshempty)
      (coe r r' (bindI "i" \i -> a ∙ i ∙ j) (papp (lhs ∙ r) (rhs ∙ r) p j))

  -- hcom r r' (lhs ={j.A j} rhs) [α i. t i] base =
  --   λ j*. hcom r r' (A j) [j=0 i. lhs; j=1 i. rhs; α i. t i j] (base j)
  ICHComPath r r' a lhs rhs sys p ->
    let j = arg in
    hcom r r' (a ∙ j)
      (vshcons (ceq j I0) "i" (\_ -> lhs) $
       vshcons (ceq j I1) "i" (\_ -> rhs) $
       mapVSysHCom (\i t -> papp lhs rhs (t ∙ i) j) (frc sys))
      (papp lhs rhs p j)

  -- hcom r r' ((j : A) → B j) [α i. t i] base =
  --   λ j*. hcom
  ICHComLine r r' a sys base ->
    let j = arg in
    hcom r r' (a ∙ j) (mapVSysHCom (\i t -> lapp (t ∙ i) j) (frc sys)) (lapp base j)

  ICCoeLine r r' a p ->
    let j = arg in
    coe r r' (bindI "i" \i -> a ∙ i ∙ j) (lapp p j)

  ICConst t -> t

  -- isEquiv : (A → B) → U
  -- isEquiv A B f :=
  --     (g^1    : B → A)
  --   × (linv^2 : (x^4 : A) → Path A x (g (f x)))
  --   × (rinv^3 : (x^5 : B) → Path B (f (g x)) x)
  --   × (coh    : (x^6 : A) →
  --             PathP (i^7) (Path B (f (linv x {x}{g (f x)} i)) (f x))
  --                   (refl B (f x))
  --                   (rinv (f x)))

  ICIsEquiv7 b f g linv x ->
    let ~i   = arg
        ~fx  = f ∙ x
        ~gfx = g ∙ fx  in
    path b (f ∙ papp x gfx (linv ∙ x) i) fx

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
                                      ;l=0 i. ffill i x
                                      ;l=1 i. rinvfill i (ffill i x) k]
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

    in VPLam lhs rhs $ NICl "k" $ ICCoeCoh2 a r r' x l

  ICCoeCoh2 a r r' x l ->
    let k = arg in
    coeCoherence a r r' x l k

  -- (λ k. rinvfill a r r' (ffill a r r' x) k)
  ICCoeCoh0Rhs a r r' x ->
    let k = arg in
    rinvfill a r r' (ffill a r r' x) k

-- | sym (A : U)(x y : A) -> x = y : y = x
--     := λ i*. hcom 0 1 [i=0 j. p j; i=1 j. x] x;
  ICSym a x y p ->
    let i = frc arg in
    hcomd I0 I1 a
          (vshcons (ceq i I0) "j" (\j -> papp x y p j) $
           vshcons (ceq i I1) "_" (\_ -> x) $
           vshempty)
          x

-- | comp (A : U)(x y z : A) (p : x = y) (q : y = z) : x = z
--    := λ i*. hcom 0 1 A [i=0 j. x; i=1 j. q j] (p i);
  ICTrans a x y z p q ->
    let i = arg in
    hcomd I0 I1 a
      (vshcons (ceq i I0) "_" (\_ -> x) $
       vshcons (ceq i I1) "j" (\j -> papp y z q j) $
       vshempty)
      (papp x y p i)

-- | ap (A B : U)(f : A -> B)(x y : A)(p : x = y) : f x = f y
--     := λ i*. f (p i)
  ICAp f x y p ->
    let i = arg in f ∙ papp x y p i

  ICBindI a ->
    a ∙ arg

proj1 :: NCofArg => DomArg => Name -> Val -> Val
proj1 x t = case frc t of
  VPair _ t _ -> t
  VNe t is    -> VNe (NProj1 t x) is
  v@VHole{}   -> v
  _           -> impossible
{-# inline proj1 #-}

proj2 :: NCofArg => DomArg => Name -> Val -> Val
proj2 x t = case frc t of
  VPair _ _ u -> u
  VNe t is    -> VNe (NProj2 t x) is
  v@VHole{}   -> v
  _           -> impossible
{-# inline proj2 #-}

unpack :: NCofArg => DomArg => Name -> Val -> Val
unpack x t = case frc t of
  VPack _ t -> t
  VNe t is  -> VNe (NUnpack t x) is
  v@VHole{} -> v
  _         -> impossible
{-# inline unpack #-}

-- | Apply a path.
papp :: NCofArg => DomArg => Val -> Val -> Val -> I -> Val
papp ~l ~r ~t i = case frc i of
  I0     -> l
  I1     -> r
  IVar x -> case frc t of
    VPLam _ _ t -> t ∙ IVar x
    VNe t is    -> VNe (NPApp l r t (IVar x)) (insertIVarF x is)
    v@VHole{}   -> v
    _           -> impossible
{-# inline papp #-}

lapp :: NCofArg => DomArg => Val -> I -> Val
lapp t i = case frc t of
  VLLam t   -> t ∙ i
  VNe t is  -> VNe (NLApp t i) is
  v@VHole{} -> v
  _         -> impossible
{-# inline lapp #-}

-- assumption: r /= r'
coed :: I -> I -> BindI Val -> Val -> NCofArg => DomArg => Val
coed r r' topA t = case (frc topA) ^. body of

  VPi (rebind topA -> a) (rebind topA -> b) ->
    VLam $ NCl (b^.body.name) $ CCoePi r r' a b t

  -- coe r r' (i. (x : A i) × B i x) t =
  -- (coe r r' A t.1, coe r r' (i. B i (coe r i A t.1)) t.2)
  VSg (rebind topA -> a) (rebind topA -> b) ->
    let t1 = proj1 (b^.body.name) t
        t2 = proj2 (b^.body.name) t

    in VPair (b^.body.name)
             (coed r r' a t1)
             (coed r r' (bindI "j" \j -> b ∙ j ∙ coe r j a t1) t2)

  VPath (rebind topA -> a) (rebind topA -> lhs) (rebind topA -> rhs) ->
        VPLam (lhs ∙ r') (rhs ∙ r')
      $ NICl (a^.body.name)
      $ ICCoePath r r' a lhs rhs t

  VLine (rebind topA -> a) ->
        VLLam
      $ NICl (a^.body.name)
      $ ICCoeLine r r' a t

  VU ->
    t

  -- closed inductives
  VTyCon x ENil ->
    t

  a@(VTyCon x (rebind topA -> ps)) -> case frc t of
    VDCon dci sp ->
      VDCon dci (coeindsp r r' ps sp (dci^.fieldTypes))
    t@(VNe _ is) ->
      VNe (NCoe r r' (rebind topA a) t) (insertI r $ insertI r' is)
    t@(VHCom _ _ _ _ _ is) ->
      VNe (NCoe r r' (rebind topA a) t) (insertI r $ insertI r' is)
    v@VHole{} ->
      v
    _ ->
      impossible

  -- NOTE: deleting the bound var from is
  a@(VNe _ is) ->
    VNe (NCoe r r' (rebind topA a) t)
        (insertI r $ insertI r' (deleteIS (topA^.binds) is))


{-
- coe Glue with unfolded and optimized hcom over fibers


coe r r' (i. Glue (A i) [(α i). (T i, f i)]) gr =

  Ar' = A r'
  sysr = [(α r). (T r, f r)]    -- instantiate system to r

  ar' : Ar'
  ar' := com r r' (i. A i) [(∀i.α) i. f i (coe r i (i.T i) gr)] (unglue gr sysr)

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
    fibval* = hcom 1 0 Tr' valSys fibval

    -- this should be a metatheoretic (I → Ar') function, because we only need it applied
    -- to the "i" variable in the end result. For clarity though, it's good to write it as a path here.

    fibpath* : fr' fibval = ar'
    fibpath* = λ j.
       hcom 1 0 Ar' [j=0    i. fr' (hcom 1 i Tr' valSys fibval)    -- no need to force valSys because
                    ;j=1    i. ar'                                 -- it's independent from j=0
                    ;r=r'   i. fr'.coh gr i j
                    ;(∀i.α) i. fr'.coh (coe r r' (i. T i) gr) i j]
                    (fibpath {fr' fibval} {ar'} j)

    -- one output system is a NeSys containing fibval*
    -- the other is NeSysHCom with fibpath* applied to the binder

  Result :=
    glue (hcom 1 0 Ar' [r=r' j. unglue gr sysr; αr' j. fibpath* j] ar')
         [αr'. fibval*]

-}

  VGlueTy (rebind topA -> a) (WIS (rebind topA -> topSys) (rebind topA -> is)) -> let

    gr           = t
    _Ar'         = a ∙ r'
    ~topSysr     = topSys ∙ r  :: NeSys
    topSysr'     = topSys ∙ r' :: NeSys
    forallTopSys = forallNeSys topSys
    topSysr'f    = frc topSysr'

  -- ar' : Ar'
  -- ar' := comp r r' (i. A i) [(∀i.α) i. f i (coe r i (j. T j) gr)] (unglue gr sysr)
    ~ar' = hcomdn r r' _Ar'
             (mapNeSysHCom'
                (\i tf -> coe i r' a (  proj1 "f" (proj2 "Ty" (tf ∙ i))
                                      ∙ coe r i (proj1BindIFromLazy "Ty" tf) gr))
                forallTopSys)
             (coed r r' a (unglue gr (frc topSysr)))

    mkComponent :: NCofArg => Val -> (Val, BindILazy Val)
    mkComponent tfr' = let

      equiv1   = tfr'
      equiv2   = proj2 "Ty"   equiv1
      equiv3   = proj2 "f"    equiv2
      equiv4   = proj2 "g"    equiv3
      ~equiv5  = proj2 "linv" equiv4

      tr'      = proj1 "Ty"   equiv1
      fr'      = proj1 "f"    equiv2
      fr'inv   = proj1 "g"    equiv3
      ~r'linv  = proj1 "linv" equiv4
      ~r'rinv  = proj1 "rinv" equiv5
      ~r'coh   = unpack "coh" (proj2 "rinv"  equiv5)

      ~fibval  = fr'inv ∙ ar'
      ~fibpath = r'rinv ∙ ar'

      ~forallTopSysf = frc forallTopSys

      -- shorthands for path applications
      app_r'linv :: NCofArg => Val -> I -> Val
      app_r'linv ~x i =
        papp x (fr'inv ∙ (fr' ∙ x)) (r'linv ∙ x) i

      app_r'coh :: NCofArg => Val -> I -> I -> Val
      app_r'coh ~x i j =
        papp (fr' ∙ app_r'linv x i)
             (fr' ∙ x)
             (papp (refl (fr' ∙ x)) (r'rinv ∙ (fr' ∙ x)) (r'coh ∙ x) i)
             j

      -- valSys should be fine without NCof polymorphism

      -- valSys = [r=r'  i. fr'.linv gr i
      --         ;(∀i.α) i. fr'.linv (coe r r' (i. T i) gr) i]
      ~valSys =
          vshcons (ceq r r') "i" (\i -> app_r'linv gr i) $
          mapVSysHCom (\i tf -> app_r'linv (coe r r' (proj1BindIFromLazy "Ty" tf) gr) i) $
          forallTopSysf


      -- fibval* : Tr'
      -- fibval* = hcom 1 0 Tr' valSys fibval
      ~fibval' = hcomd I1 I0 tr' valSys fibval

      -- fibpath* : fr' fibval = ar'
      -- fibpath* = λ j.
      --    hcom 1 0 Ar' [j=0    i. fr' (hcom 1 i Tr' valSys fibval)    -- no need to force valSys because
      --                 ;j=1    i. ar'                                 -- it's independent from j=0
      --                 ;r=r'   i. fr'.coh gr i j
      --                 ;(∀i.α) i. fr'.coh (coe r r' (i. T i) gr) i j]
      --                 (fibpath {fr' fibval} {ar'} j)

      fibpath' =
        bindILazy "j" \j ->
        hcomd I1 I0 _Ar'
          (vshcons (ceq j I0) "i" (\i -> fr' ∙ hcom I1 i tr' valSys fibval) $
           vshcons (ceq j I1) "i" (\i -> ar') $
           vshcons (ceq r r') "i" (\i -> app_r'coh gr i j) $
           mapVSysHCom (\i tf -> app_r'coh (coe r r' (proj1BindIFromLazy "Ty" tf) gr) i j) $
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
      VSNe (WIS sys is) -> let
        (!fibvals, !fibpaths) = mkNeSystems sys
        in VSNe (WIS fibvals is) // VSHNe (WIS fibpaths is)

    -- glue (hcom 1 0 Ar' [r=r' j. unglue gr sysr; αr' j. fibpath* j] ar')
    --      [αr'. fibval*]
    in glue
         (hcomd I1 I0 _Ar' (vshcons (ceq r r') "i" (\i -> unglue gr (frc topSysr)) fibpaths) ar')
         topSysr'f
         fibvals

  -- coe r r' (i. Wrap x (a i)) t = pack (coe r r' (i. a i) (t.unpackₓ))
  VWrap x (rebind topA -> a) ->
    VPack x $ coed r r' a (unpack x t)

  VHTyCon _ ENil ->
    t

  a@(VHTyCon ti (rebind topA -> ps)) -> case frc t of

    t@(VHDCon di _ fs s is) ->
      let psr' = ps ∙ r' in
      if di^.isCoherent then
        VHDCon di psr' (coeindsp r r' ps fs (di^.fieldTypes)) s is
      else
        case coehindsp r r' (rebind topA a) ps fs (di^.fieldTypes) s (di^.boundary) of
          (!sp, !sys) ->
            VHCom r' r (VHTyCon ti psr')
              (WIS sys is)
              (VHDCon di psr' sp s is)
              (insertI r $ insertI r' is)

    -- coe r r' a (fhcom i j (a r) [α k. t k] b) =
    -- fhcom i j (a r') [α k. coe r r' a (t k)] (coe r r' a b)
    t@(VHCom i j _ sys b is) ->
      let abind = rebind topA a in
      VHCom i j
        (VHTyCon ti (ps ∙ r'))
        (mapNeSysHCom' (\k t -> coed r r' abind (t ∙ k)) sys)
        (coed r r' abind b)
        is

    t@(VNe n is) ->
      VNe (NCoe r r' (rebind topA a) t) (insertI r $ insertI r' is)

    t@VHole{} ->
      t

    v -> error (
           "\n" ++
           show ?dom ++ "\n" ++ show ?cof ++ "\n" ++
           take 100000 (show v) ++ "\n\n\n" ++ take 200 (show ps)
           )
    -- _ ->
    --   impossible

  v@VHole{} -> v

  v ->
    error $ take 1000 $ show v
    -- VHole (VErrHole $ take 300 $ show v)
    -- impossible


coe :: NCofArg => DomArg => I -> I -> BindI Val -> Val -> Val
coe r r' ~a t
  | frc r == frc r' = t
  | True            = coed r r' a t
{-# inline coe #-}

-- vhcom :: I -> I -> VTy -> NeSysHCom' -> Val -> IVarSet -> Val
-- vhcom r r' a sys base ~is = case sys^.body of
--   NSHEmpty -> base
--   _        -> VHCom r r' a sys base is
-- {-# inline vhcom #-}

vhcom :: I -> I -> VTy -> NeSysHCom' -> Val -> IVarSet -> Val
vhcom = VHCom
{-# inline vhcom #-}

-- | HCom with off-diagonal I args ("d") and neutral system arg ("n").
hcomdn :: I -> I -> Val -> NeSysHCom' -> Val -> NCofArg => DomArg => Val
hcomdn r r' topA ts@(WIS nts is) base = case frc topA of
  VPi a b ->
    VLam $ NCl (b^.name) $ CHComPi r r' a b nts base

  VSg a b ->
    VPair
      (b^.name)
      (hcomdn r r' a
        (mapNeSysHCom' (\i t -> proj1 (b^.name) (t ∙ i)) ts)
        (proj1 (b^.name) base))

      (hcomdn r r'
        (b ∙ hcomdn r r' a
             (mapNeSysHCom' (\i t -> proj1 (b^.name) (t ∙ i)) ts)
             (proj1 (b^.name) base))

        (mapNeSysHCom'
          (\i t ->
           coe i r'
             (bindI "i" \i ->
                b ∙ hcom r i a
                     (mapVSysHCom (\i t -> proj1 (b^.name) (t ∙ i)) (frc ts))
                     (proj1 (b^.name) base))
             (proj2 (b^.name) (t ∙ i)))
          ts)

        (coed r r'
           (bindI "i" \i ->
              b ∙ hcomn r i a
                   (mapNeSysHCom' (\i t -> proj1 (b^.name) (t ∙ i)) ts)
                   (proj1 (b^.name) base))
           (proj2 (b^.name) base)))

  -- (  hcom r r' A [α i. (t i).1] b.1
  --  , com r r' (i. B (hcom r i A [α j. (t j).1] b.1)) [α i. (t i).2] b.2)

  VPath a lhs rhs ->
        VPLam lhs rhs
      $ NICl (a^.name)
      $ ICHComPath r r' a lhs rhs nts base

  a@(VNe n is') ->
    vhcom r r' a ts base (insertI r $ insertI r' $ is <> is')

  -- hcom r r' U [α i. t i] b =
  --   Glue b [r=r'. (b, idEquiv); α. (t r', (coe r' r (i. t i), coeIsEquiv))]

  VU -> let

    -- NOTE: r = r' can be false or neutral
    sys = nscons (ceq r r') (VPair "Ty" base (theIdEquiv base)) $
          mapNeSysFromH
            (\t -> VPair "Ty" (t ∙ r') (theCoeEquiv (bindIUnLazy t) r' r))
            -- (\t -> VPair "Ty" (t ∙ r') (theCoeEquiv (bindI (t^.name) \i -> t ∙ i) r' r))
            nts

    in VGlueTy base (WIS sys (insertI r (insertI r' is)))

-- hcom for Glue
--------------------------------------------------------------------------------

  -- hcom r r' (Glue [α. (T, f)] A) [β i. t i] gr =
  --   glue (hcom r r' A [β i. unglue (t i); α i. f (hcom r i T [β j. t j] gr)] (unglue gr))
  --        [α. hcom r r' T [β i. t i] gr]

  VGlueTy a alphasys ->
    let gr      = base
        betasys = ts

            -- [α. hcom r r' T [β i. t i] gr]
        fib = mapNeSys' (\t -> hcom r r' (proj1 "Ty" t) (frc betasys) gr) alphasys

        -- hcom r r' A [  β i. unglue (t i)
        --              ; α i. f (hcom r i T [β. t] gr)]
        --             (unglue gr)
        hcombase =
          hcomdn r r' a
            (catNeSysHCom'
               (mapNeSysHCom' (\i t -> unglue (t ∙ i) (frc alphasys)) betasys)
               (mapNeSysToH'  (\i tf -> proj1 "f" (proj2 "Ty" tf)
                                      ∙ hcom r i (proj1 "Ty" tf) (frc betasys) gr) alphasys))
            (ungluen gr alphasys)

    in VGlue hcombase alphasys (fib^.body)
             (insertI r $ insertI r' ((alphasys^.ivars) <> (betasys^.ivars)))

  VLine a ->
        VLLam
      $ NICl (a^.name)
      $ ICHComLine r r' a nts base

  -- hcom r r' (x : A) [β i. t i] base =
  --   pack (hcom r r' A [β i. (t i).unpackₓ] (base.unpackₓ))
  VWrap x a ->
    VPack x $ hcomdn r r' a
      (mapNeSysHCom' (\i t -> unpack x (t ∙ i)) ts)
      (unpack x base)

  a@(VTyCon _ ps) -> case frc base of
    base@(VDCon dci sp) -> case ?dom of
      0 ->
        VDCon dci (hcomind0sp r r' a ts ps (dci^.conId) 0 sp (dci^.fieldTypes))
      _ -> case projsys' (dci^.conId) ts of
        TTPProject prj  ->
          VDCon dci (hcomindsp r r' a (WIS prj (ts^.ivars)) ps (dci^.conId) 0 sp (dci^.fieldTypes))
        TTPNe (WIS sys is) -> -- NOTE: this "is" is extended with the blocking neutral component's ivars
          vhcom r r' a (WIS sys is) base (insertI r $ insertI r' is)

    base@(VNe n is') ->
      vhcom r r' a ts base (insertI r $ insertI r' $ is <> is')

    base@(VHCom _ _ _ _ _ is') ->
      vhcom r r' a ts base (insertI r $ insertI r' $ is <> is')

    base@VHole{} -> base
    _            -> impossible


  -- "fhcom", hcom on HITs is blocked
  a@(VHTyCon tyinf ps) ->
    vhcom r r' a ts base (insertI r $ insertI r' is)

  v@VHole{} -> v

  _ ->
    impossible


----------------------------------------------------------------------------------------------------

-- | HCom with nothing known about semantic arguments.
hcom :: NCofArg => DomArg => I -> I -> Val -> VSysHCom -> Val -> Val
hcom r r' ~a ~t ~b
  | frc r == frc r' = b
  | True = case t of
      VSHTotal v -> v ∙ r'
      VSHNe sys  -> hcomdn r r' a sys b
{-# inline hcom #-}

-- | HCom with neutral system input.
hcomn :: NCofArg => DomArg => I -> I -> Val -> NeSysHCom' -> Val -> Val
hcomn r r' ~a ~sys ~b
  | frc r == frc r' = b
  | True            = hcomdn r r' a sys b
{-# inline hcomn #-}

-- | Off-diagonal HCom.
hcomd :: NCofArg => DomArg => I -> I -> Val -> VSysHCom -> Val -> Val
hcomd r r' ~a ~sys ~b = case sys of
  VSHTotal v -> v ∙ r'
  VSHNe sys  -> hcomdn r r' a sys b
{-# inline hcomd #-}

glueTy :: NCofArg => DomArg => Val -> VSys -> Val
glueTy ~a sys = case sys of
  VSTotal b -> proj1 "Ty" b
  VSNe sys  -> VGlueTy a sys
{-# inline glueTy #-}

glue :: Val -> VSys -> VSys -> Val
glue ~t eqs sys = case (eqs, sys) of
  (VSTotal{}, VSTotal v)         -> v
  (VSNe eqs , VSNe (WIS sys is)) -> VGlue t eqs sys is
  _                              -> impossible
{-# inline glue #-}

unglue :: NCofArg => DomArg => Val -> VSys -> Val
unglue ~t sys = case sys of
  VSTotal teqv -> proj1 "f" (proj2 "Ty" teqv) ∙ t
  VSNe sys     -> ungluen t sys
{-# inline unglue #-}

-- | Unglue with neutral system arg.
ungluen :: NCofArg => DomArg => Val -> NeSys' -> Val
ungluen t (WIS sys is) = case frc t of
  VGlue base _ _ _        -> base
  VNe n is'               -> VNe (NUnglue n sys) (is <> is')
  v@VHole{}               -> v
  v                       -> error ("ungluen:  " ++ take 1000 (show v))
  -- v                       -> impossible
{-# inline ungluen #-}


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
  DontRecurse -> VNe (NDontRecurse inf) mempty
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
  _:is -> freshI \v -> pushIVars (s `ext` v) is

pushSp :: Env -> VDSpine -> Env
pushSp env = \case
  VDNil       -> env
  VDCons v sp -> pushSp (EDef env v) sp

lookupCase :: EvalArgs (Lvl -> VDSpine -> Cases -> Val)
lookupCase i sp cs = case i // cs of
  (0, CSCons _ _  body cs) -> let ?env = pushSp ?env sp in eval body
  (i, CSCons _ _  _    cs) -> lookupCase (i - 1) sp cs
  _                        -> impossible

case_ :: NCofArg => DomArg => (Val -> NamedClosure -> CaseTag -> EvalClosure Cases -> Val)
case_ t b tag ecs@(EC sub env rc cs) = case frc t of
  VDCon dci sp           -> let ?sub = wkSub sub; ?env = env; ?recurse = rc in lookupCase (dci^.conId) sp cs
  n@(VNe _ is)           -> VNe (NCase n b tag ecs) is
  n@(VHCom _ _ _ _ _ is) -> VNe (NCase n b tag ecs) is
  v@VHole{}              -> v
  _                      -> impossible
{-# inline case_ #-}

projVDSpine :: Lvl -> VDSpine -> Val
projVDSpine x sp = case (x, sp) of
  (0, VDCons t _ ) -> t
  (x, VDCons _ sp) -> projVDSpine (x - 1) sp
  _                -> impossible

lazyprojfield :: NCofArg => DomArg => Lvl -> Lvl -> Val -> Val
lazyprojfield conid fieldid v = case frc v of
  VDCon dci sp | conid == (dci^.conId) -> projVDSpine fieldid sp
  _                                    -> impossible
{-# inline lazyprojfield #-}

lazyprojsys :: NCofArg => DomArg => Lvl -> Lvl -> NeSysHCom -> NeSysHCom
lazyprojsys conid fieldid = \case
  NSHEmpty      -> NSHEmpty
  NSHCons t sys -> NSHCons (mapBindCof t \t -> umapBindILazy t (\_ -> lazyprojfield conid fieldid))
                           (lazyprojsys conid fieldid sys)

lazyprojsys' :: NCofArg => DomArg => Lvl -> Lvl -> NeSysHCom' -> NeSysHCom'
lazyprojsys' conid fieldid (WIS sys is) = WIS (lazyprojsys conid fieldid sys) is
{-# inline lazyprojsys' #-}

hcomind0sp :: NCofArg => DomArg => I -> I -> Val -> NeSysHCom' -> Env -> Lvl -> Lvl -> VDSpine -> Tel -> VDSpine
hcomind0sp r r' a sys params conid fieldid sp fieldtypes = case (sp, fieldtypes) of
  (VDNil, TNil) ->
    VDNil
  (VDCons t sp, TCons _ tty fieldtypes) ->
    VDCons (hcomdn r r' (evalIndParam params tty) (lazyprojsys' conid fieldid sys) t)
           (hcomind0sp r r' a sys (EDef params t) conid (fieldid + 1) sp fieldtypes)
  _ ->
    impossible

-- System where all components are known to be the same constructor
data Projected
  = PNil
  | PCons NeCof Name IVar VDSpine Projected
  deriving Show

type Projected' = WithIS Projected

-- TODO: unbox
data TryToProject
  = TTPProject Projected
  | TTPNe {-# unpack #-} NeSysHCom'
  deriving Show

projsys :: NCofArg => DomArg => Lvl -> NeSysHCom' -> NeSysHCom -> TryToProject
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
      VNe n is -> TTPNe (WIS (topSys^.body) (deleteIS (t^.body.binds) is <> topSys^.ivars))

      VHole{}  -> error "TODO: hole in system projection"
      _        -> impossible

projsys' :: NCofArg => DomArg => Lvl -> NeSysHCom' -> TryToProject
projsys' conix (WIS sys is) = projsys conix (WIS sys is) sys
{-# inline projsys' #-}

projfields :: Projected -> Lvl -> NeSysHCom
projfields prj fieldid = case prj of
  PNil                  -> NSHEmpty
  PCons ncof x i sp prj -> NSHCons (BindCof ncof (BindILazy x i (projVDSpine fieldid sp)))
                                   (projfields prj fieldid)

projfields' :: Projected' -> Lvl -> NeSysHCom'
projfields' (WIS prj is) fieldid = WIS (projfields prj fieldid) is
{-# inline projfields' #-}

hcomindsp :: NCofArg => DomArg => I -> I -> Val -> Projected' -> Env -> Lvl -> Lvl -> VDSpine -> Tel -> VDSpine
hcomindsp r r' a prj params conid fieldid sp fieldtypes = case (sp, fieldtypes) of
  (VDNil, TNil) ->
    VDNil
  (VDCons t sp, TCons _ tty fieldtypes) ->
    VDCons (hcomdn r r' (evalIndParam params tty) (projfields' prj fieldid) t)
           (hcomindsp r r' a prj (EDef params t) conid (fieldid + 1) sp fieldtypes)
  _ ->
    impossible

coeindsp :: NCofArg => DomArg => I -> I -> BindI Env -> VDSpine -> Tel -> VDSpine
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
data VBoundary = VBTotal Val | VBNe IVarSet deriving Show

vbempty :: VBoundary
vbempty = VBNe mempty

vbcons :: NCofArg => VCof -> (NCofArg => Val) -> VBoundary -> VBoundary
vbcons cof v ~sys = case cof of
  VCTrue      -> VBTotal v
  VCFalse     -> sys
  VCNe cof is -> case sys of
    VBTotal v'  -> VBTotal v'
    VBNe is'    -> VBNe (is <> is')
{-# inline vbcons #-}

evalBoundary :: EvalArgs (Sys -> VBoundary)
evalBoundary = \case
  SEmpty          -> VBNe mempty
  SCons cof t sys -> vbcons (evalCof cof) (eval t) (evalBoundary sys)

hdcon :: NCofArg => DomArg => HDConInfo -> Env -> VDSpine -> Sub -> Val
hdcon inf ps fs s = case inf^.boundary of
  SEmpty -> VHDCon inf ps fs s mempty
  bnd    -> let ?sub = s; ?env = pushSp ps fs; ?recurse = DontRecurse in
            case evalBoundary bnd of
              VBTotal v -> v
              VBNe is   -> VHDCon inf ps fs s is
{-# inline hdcon #-}

lookupHCase :: EvalArgs (Lvl -> VDSpine -> Sub -> HCases -> Val)
lookupHCase i sp s cs = case i // cs of
  (0, HCSCons _ _ _ body cs) -> let ?env = pushSp ?env sp; ?sub = pushSub ?sub s in
                                eval body
  (i, HCSCons _ _ _ _    cs) -> lookupHCase (i - 1) sp s cs
  _                          -> impossible

sysCofs :: NeSys -> [NeCof]
sysCofs = \case
  NSEmpty -> []
  NSCons t cs -> t^.binds : sysCofs cs

hcase :: NCofArg => DomArg => (Val -> NamedClosure -> CaseTag -> EvalClosure HCases -> Val)
hcase t b tag ecs@(EC sub env rc cs) = case frc t of

  VHDCon i ps fs s _ ->
    let ?sub = wkSub sub; ?env = env; ?recurse = rc in
    lookupHCase (i^.conId) fs s cs

  t@(VHCom r r' a sys base is) ->

     -- case (hcom r r' a [α i. t i] base) B cs =
     -- let B* = λ i. B (hcom r i a [α i. t i] base);
     -- hcom r r' (B (hcom r r' a [α i. t i] base))
     --           [α i. coe i r' B* (case (t i) B cs)]
     --           (coe r r' B* (case base B cs))
    let bbind = bindI "i" \i -> b ∙ hcom r i a (frc sys) base in
    hcomdn r r' (b ∙ t)
      (mapNeSysHCom' (\i t -> coe i r' bbind (hcase (t ∙ i) b tag ecs)) sys)
      (coed r r' bbind (hcase base b tag ecs))

  n@(VNe _ is) -> VNe (NHCase n b tag ecs) is
  v@VHole{}    -> v
  v            -> error $ take 1000 $ show v

evalCoeBoundary :: EvalArgs (I -> IVar -> BindI VTy -> Sys -> NeSysHCom)
evalCoeBoundary r' i a = \case
  SEmpty ->
    NSHEmpty
  SCons cof t bnd -> case evalCof cof of
    VCTrue     -> impossible
    VCFalse    -> evalCoeBoundary r' i a bnd
    VCNe cof _ -> NSHCons (bindCof cof (BindILazy (a^.name) i (coe (IVar i) r' a (eval t))))
                          (evalCoeBoundary r' i a bnd)

coehindsp :: NCofArg => DomArg =>
   I -> I -> BindI VTy -> BindI Env -> VDSpine -> Tel -> Sub -> Sys -> (VDSpine, NeSysHCom)
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

evalIClosure :: EvalArgs (Name -> Tm -> NamedIClosure)
evalIClosure x a = NICl x (ICEval ?sub ?env ?recurse a)
{-# inline evalIClosure #-}

eval :: EvalArgs (Tm -> Val)
eval = \case
  TopVar inf         -> inf^.defVal
  RecursiveCall inf  -> recursiveCall inf
  LocalVar x         -> localVar x
  Let x _ t u        -> define (eval t) (eval u)

  -- Inductives
  TyCon i ts         -> VTyCon i (params ts)
  DCon i sp          -> VDCon i (spine sp)
  Case t x b tag cs  -> case_ (eval t) (evalClosure x b) tag (EC ?sub ?env ?recurse cs)
  Split x b tag cs   -> VLam $ NCl x $ CSplit (evalClosure x b) tag (EC ?sub ?env ?recurse cs)
  HSplit x b tag cs  -> VLam $ NCl x $ CHSplit (evalClosure x b) tag (EC ?sub ?env ?recurse cs)
  HTyCon i ts        -> VHTyCon i (params ts)
  HDCon i ps fs s    -> hdcon i (lazyParams ps) (spine fs) (sub s)
  HCase t x b tag cs -> hcase (eval t) (evalClosure x b) tag (EC ?sub ?env ?recurse cs)

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
  HCom r r' a t b    -> hcom' (evalI r) (evalI r') (eval a) (evalSysHCom' t) (eval b)

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
  Hole h             -> case h of SrcHole x p -> VHole (VSrcHole x p ?sub ?env)
                                  ErrHole msg -> VHole (VErrHole msg)

  -- Builtins
  Refl t             -> refl (eval t)
  Sym a x y p        -> sym (eval a) (eval x) (eval y) (eval p)
  Trans a x y z p q  -> trans (eval a) (eval x) (eval y) (eval z) (eval p) (eval q)
  Ap f x y p         -> ap_ (eval f) (eval x) (eval y) (eval p)
  Com r r' i a t b   -> com' (evalI r) (evalI r') (bindIS i \_ -> eval a) (evalSysHCom' t) (eval b)

----------------------------------------------------------------------------------------------------
-- Forcing
----------------------------------------------------------------------------------------------------

class Force a b | a -> b where
  frc  :: NCofArg => DomArg => a -> b           -- force a value wrt current cof. Idempotent when
                                                -- the type is (a -> a).
  frcS :: SubArg => NCofArg => DomArg => a -> b -- apply a substitution and then force. It's always
                                                -- an *error* to apply it multiple times.


instance Force I I where
  frc  i = doSub ?cof i;              {-# inline frc #-}
  frcS i = doSub ?cof (doSub ?sub i); {-# inline frcS #-}

instance Force Sub Sub where
  frc  s = doSub ?cof s; {-# inline frc #-}
  frcS s = doSub ?cof (doSub ?sub s); {-# inline frcS #-}

instance Force NeCof VCof where
  frc = \case
    NCEq i j    -> ceq (frc i) (frc j)
    NCAnd c1 c2 -> case frc c1 of
      VCTrue -> frc c2
      VCFalse -> VCFalse
      VCNe cof is -> let ?cof = cof^.extended in case frc c2 of
        VCTrue        -> VCNe cof is
        VCFalse       -> VCFalse
        VCNe cof' is' -> VCNe (NeCof' (cof'^.extended) (NCAnd (cof^.extra) (cof'^.extra)))
                              (is <> is')

  frcS = \case
    NCEq i j    -> ceq (frcS i) (frcS j)
    NCAnd c1 c2 -> case frcS c1 of
      VCTrue  -> frcS c2
      VCFalse -> VCFalse
      VCNe cof is -> let ?cof = cof^.extended in case frcS c2 of
        VCTrue        -> VCNe cof is
        VCFalse       -> VCFalse
        VCNe cof' is' -> VCNe (NeCof' (cof'^.extended) (NCAnd (cof^.extra) (cof'^.extra)))
                              (is <> is')

instance Force Val Val where
  frc = \case
    VSub v s                                -> let ?sub = wkSub s in frcS v
    VNe t is               | isUnblocked is -> frc t
    VGlueTy a (WIS sys is) | isUnblocked is -> frc (glueTy a (frc sys))
    VHDCon i ps fs s is    | isUnblocked is -> frc (hdcon i ps fs s)
    VHCom r r' a sys t is  | isUnblocked is -> frc (hcom r r' a (frc sys) t)
    VGlue t eqs sys is     | isUnblocked is -> frc (glue t (frc eqs) (frc sys))
    v                                       -> v

  frcS = \case
    VSub v s                                 -> let ?sub = sub s in frcS v
    VNe t is               | isUnblockedS is -> frcS t
    VGlueTy a (WIS sys is) | isUnblockedS is -> frc (glueTy (sub a) (frcS sys))
    VHDCon i ps fs s is    | isUnblockedS is -> frc (hdcon i (sub ps) (sub fs) (sub s))
    VHCom r r' a sys t is  | isUnblockedS is -> frc (hcom (sub r) (sub r') (sub a) (frcS sys) (sub t))
    VGlue t eqs sys is     | isUnblockedS is -> frc (glue (sub t) (frcS eqs) (frcS sys))


    VNe t is              -> VNe (sub t) (sub is)
    VGlueTy a sys         -> VGlueTy (sub a) (sub sys)
    VGlue t eqs sys is    -> VGlue (sub t) (sub eqs) (sub sys) (sub is)
    VPi a b               -> VPi (sub a) (sub b)
    VLam t                -> VLam (sub t)
    VPath a t u           -> VPath (sub a) (sub t) (sub u)
    VPLam l r t           -> VPLam (sub l) (sub r) (sub t)
    VSg a b               -> VSg (sub a) (sub b)
    VPair x t u           -> VPair x (sub t) (sub u)
    VWrap x t             -> VWrap x (sub t)
    VPack x t             -> VPack x (sub t)
    VU                    -> VU
    VHole h               -> VHole (frcS h)
    VLine t               -> VLine (sub t)
    VLLam t               -> VLLam (sub t)
    VTyCon x ts           -> VTyCon x (sub ts)
    VDCon ci sp           -> VDCon ci (sub sp)
    VHTyCon i ps          -> VHTyCon i (sub ps)
    VHDCon i ps fs s is   -> VHDCon i (sub ps) (sub fs) (sub s) (sub is)
    VHCom r r' a sys t is -> VHCom (sub r) (sub r') (sub a) (sub sys) (sub t) (sub is)
  {-# noinline frcS #-}

instance Force VHole VHole where
  frc h = h; {-# inline frc #-}
  frcS = \case
    VSrcHole x p s env -> VSrcHole x p (sub s) (sub env)
    VErrHole msg       -> VErrHole msg
  {-# inline frcS #-}

instance Force Ne Val where
  frc = \case
    t@NLocalVar{}     -> VNe t mempty
    t@NDontRecurse{}  -> VNe t mempty
    NSub n s          -> let ?sub = wkSub s in frcS n
    NApp t u          -> frc (frc t ∙ u)
    NPApp l r t i     -> frc (papp l r (frc t) i)
    NProj1 t x        -> frc (proj1 x (frc t))
    NProj2 t x        -> frc (proj2 x (frc t))
    NUnpack t x       -> frc (unpack x (frc t))
    NCoe r r' a t     -> frc (coe r r' (frc a) (frc t))
    NUnglue t sys     -> frc (unglue (frc t) (frc sys))
    NLApp t i         -> frc (lapp (frc t) i)
    NCase t b tag cs  -> frc (case_ (frc t) b tag cs)
    NHCase t b tag cs -> frc (hcase (frc t) b tag cs)
  {-# noinline frc #-}

  frcS = \case
    t@NLocalVar{}     -> VNe t mempty
    t@NDontRecurse{}  -> VNe t mempty
    NSub n s          -> let ?sub = sub s in frcS n
    NApp t u          -> frc (frcS t ∙ sub u)
    NPApp l r t i     -> frc (papp (sub l) (sub r) (frcS t) (frcS i))
    NProj1 t x        -> frc (proj1 x (frcS t))
    NProj2 t x        -> frc (proj2 x (frcS t))
    NUnpack t x       -> frc (unpack x (frcS t))
    NCoe r r' a t     -> frc (coe (frcS r) (frcS r') (frcS a) (frcS t))
    NUnglue t sys     -> frc (unglue (frcS t) (frcS sys))
    NLApp t i         -> frc (lapp (frcS t) (frcS i))
    NCase t b tag cs  -> frc (case_ (frcS t) (sub b) tag (sub cs))
    NHCase t b tag cs -> frc (hcase (frcS t) (sub b) tag (sub cs))

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
      VCTrue      -> VSHTotal (t^.body)
      VCFalse     -> frc sys
      VCNe cof is -> case frc sys of
        VSHTotal v'         -> VSHTotal v'
        VSHNe (WIS sys is') -> VSHNe (WIS (NSHCons (bindCof cof (t^.body)) sys) (is <> is'))

  frcS = \case
    NSHEmpty ->
      vshempty
    NSHCons t sys -> case frcS (t^.binds) of
      VCTrue      -> VSHTotal (frcS (t^.body))
      VCFalse     -> frcS sys
      VCNe cof is -> case frcS sys of
        VSHTotal v'         -> VSHTotal v'
        VSHNe (WIS sys is') ->
          VSHNe (WIS (NSHCons (bindCof cof (frcS (t^.body))) sys) (is <> is'))

-- TODO: check IVarSet
instance Force NeSysHCom' VSysHCom where
  frc sys = frc (sys^.body); {-# inline frc #-}
  frcS sys = frcS (sys^.body); {-# inline frcS #-}

-- TODO: check IVarSet
instance Force NeSys' VSys where
  frc sys = frc (sys^.body); {-# inline frc #-}
  frcS sys = frcS (sys^.body); {-# inline frcS #-}

instance Force a fa => Force (BindI a) (BindI fa) where

  frc (BindI x i a) =
    let ?cof = setDomCod (i + 1) i ?cof `ext` IVar i in
    seq ?cof (BindI x i (frc a))
  {-# inline frc #-}

  frcS (BindI x i a) =
    let fresh = dom ?cof in
    let ?sub  = setDomCod (fresh+1) i ?sub `ext` IVar fresh in
    let ?cof  = setDom (fresh+1) ?cof `ext` IVar fresh in
    seq ?sub $ seq ?cof $ BindI x fresh (frcS a)
  {-# inline frcS #-}

instance Force a fa => Force (BindILazy a) (BindILazy fa) where

  frc (BindILazy x i a) =
    let ?cof = setDomCod (i + 1) i ?cof `ext` IVar i in
    seq ?cof (BindILazy x i (frc a))
  {-# inline frc #-}

  frcS (BindILazy x i a) =
    let fresh = dom ?cof in
    let ?sub  = setDomCod (fresh+1) i ?sub `ext` IVar fresh in
    let ?cof  = setDom (fresh+1) ?cof `ext` IVar fresh in
    seq ?sub $ seq ?cof $ BindILazy x fresh (frcS a)
  {-# inline frcS #-}

----------------------------------------------------------------------------------------------------
-- Pushing neutral substitutions
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
  NCase t b tag cs   -> NCase (sub t) (sub b) tag (sub cs)
  NHCase t b tag cs  -> NHCase (sub t) (sub b) tag (sub cs)

----------------------------------------------------------------------------------------------------
-- Definitions
----------------------------------------------------------------------------------------------------

fun :: Val -> Val -> Val
fun a b = VPi a $ NCl "_" $ CConst b

funf :: Val -> Val -> Val
funf a b = VPi a $ NCl "_" $ CConst b

-- | (A : U) -> A -> A -> U
path :: Val -> Val -> Val -> Val
path a t u = VPath (NICl "_" (ICConst a)) t u

-- | (x : A) -> PathP _ x x
refl :: Val -> Val
refl ~t = VPLam t t $ NICl "_" $ ICConst t

-- | sym (A : U)(x y : A) -> x = y : y = x
--     := λ i. hcom 0 1 A [i=0. p; i=1 _. x] x;
sym :: Val -> Val -> Val -> Val -> Val
sym a ~x ~y p = VPLam x y $ NICl "i" (ICSym a x y p)

-- | comp (A : U)(x y z : A) (p : x = y) (q : y = z) : x = z
--    := λ i. hcom 0 1 A [i=0 j. x; i=1 j. q j] (p i);
trans :: Val -> Val -> Val -> Val -> Val -> Val -> Val
trans a ~x ~y ~z p q = VPLam x z $ NICl "i" $ ICTrans a x y z p q

-- | ap (A B : U)(f : A -> B)(x y : A)(p : x = y) : f x = f y
--     := λ i. f (p i)
ap_ :: NCofArg => DomArg => Val -> Val -> Val -> Val -> Val
ap_ f ~x ~y p = let ~ff = frc f in
                VPLam (ff ∙ x) (ff ∙ y) $ NICl "i" $ ICAp ff x y p

-- | (A : U)(B : U) -> (A -> B) -> U
isEquiv :: Val -> Val -> Val -> Val
isEquiv a b f = VSg (fun b a) $ NCl "g" $ CIsEquiv1 a b f

-- | U -> U -> U
equiv :: Val -> Val -> Val
equiv a b = VSg (fun a b) $ NCl "f" $ CEquiv a b

-- | U -> U
equivInto :: Val -> Val
equivInto a = VSg VU $ NCl "Ty" $ CEquivInto a

-- | idIsEquiv : (A : U) -> isEquiv (\(x:A).x)
idIsEquiv :: Val -> Val
idIsEquiv a =
  VPair "g"    (VLam $ NCl "a" C'λ'a''a)     $
  VPair "linv" (VLam $ NCl "a" C'λ'a'i''a)   $
  VPair "rinv" (VLam $ NCl "b" C'λ'a'i''a)   $
  VPack "coh"  (VLam $ NCl "a" C'λ'a'i'j''a)

-- | Identity function packed together with isEquiv.
theIdEquiv :: Val -> Val
theIdEquiv a = VPair "f" (VLam $ NCl "x" C'λ'a''a) (idIsEquiv a)


-- Coercion is an equivalence
----------------------------------------------------------------------------------------------------

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
                                      ;l=0 i. ffill i x
                                      ;l=1 i. rinvfill i (ffill i x) k]
                                      x
-}

ffill :: NCofArg => DomArg => BindI Val -> I -> I -> Val -> Val
ffill a r i x = coe r i a x; {-# inline ffill #-}

gfill :: NCofArg => DomArg => BindI Val -> I -> I -> Val -> Val
gfill a r i x = coe i r a x; {-# inline gfill #-}

linvfill :: NCofArg => DomArg => BindI Val -> I -> I -> Val -> I -> Val
linvfill a r i x j =
  hcom r i (a ∙ r)
    (vshcons (ceq j I0) "k" (\_ -> x) $
     vshcons (ceq j I1) "k" (\k -> coe k r a (coe r k a x)) $
     vshempty)
    x

rinvfill :: NCofArg => DomArg => BindI Val -> I -> I -> Val -> I -> Val
rinvfill a r i x j =
  hcom i r (a ∙ i)
    (vshcons (ceq j I0) "k" (\k -> coe k i a (coe i k a x)) $
     vshcons (ceq j I1) "k" (\_ -> x) $
     vshempty)
    x

coeCoherence :: NCofArg => DomArg => BindI Val -> I -> I -> Val -> I -> I -> Val
coeCoherence a r r' x l k =
  hcom r r' (a ∙ r')
    (vshcons (ceq k I0) "i" (\i -> coe i r' a (ffill a r i (linvfill a r i x l))) $
     vshcons (ceq k I1) "i" (\i -> coe i r' a (ffill a r i x)) $
     vshcons (ceq l I0) "i" (\i -> coe i r' a (ffill a r i x)) $
     vshcons (ceq l I1) "i" (\i -> coe i r' a (rinvfill a r i (ffill a r i x) k)) $
     vshempty)
    (coe r r' a x)

coeIsEquiv :: BindI Val -> I -> I -> Val
coeIsEquiv a r r' =
  VPair "g"    (VLam $ NCl "x" $ CCoeAlong a r' r) $
  VPair "linv" (VLam $ NCl "x" $ CCoeLinv0 a r r') $
  VPair "rinv" (VLam $ NCl "x" $ CCoeRinv0 a r r') $
  VPack "coh"  (VLam $ NCl "x" $ CCoeCoh0  a r r')

-- | Coercion function packed together with isEquiv.
theCoeEquiv :: BindI Val -> I -> I -> Val
theCoeEquiv a r r' = VPair "f" (VLam $ NCl "x" $ CCoeAlong a r r') (coeIsEquiv a r r')
