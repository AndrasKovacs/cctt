
module Core where

import Common
import CoreTypes
import Interval

import Debug.Trace

----------------------------------------------------------------------------------------------------
{-
FORCING GUIDELINE
  - Always forced:
    - VSys, NeSys', NeSysHCom', NeCof, IVar

  - if a function name ends on "F", it has forcing preconditions
  - Semantic Cof/I functions return forced results.

  - moving under cofibrations:
    - WE LOSE OFF-DIAGONALS
    - WE LOSE SYSTEM FORCING

-}

----------------------------------------------------------------------------------------------------
-- Context manipulation primitives
----------------------------------------------------------------------------------------------------

-- | Get a fresh ivar when not working under a Sub.
freshI :: (NCofArg => IVar -> a) -> (NCofArg => a)
freshI act =
  let fresh = dom ?cof in
  let ?cof  = setDom (fresh+1) ?cof `ext` IVar fresh in
  seq ?cof (act fresh)
{-# inline freshI #-}

-- | Get a fresh ivar, when working under a Sub.
freshIS :: (SubArg => NCofArg => IVar -> a) -> (SubArg => NCofArg => a)
freshIS act =
  let fresh = dom ?cof in
  let ?sub  = setDom (fresh+1) ?sub `ext` IVar fresh in
  let ?cof  = setDom (fresh+1) ?cof `ext` IVar fresh in
  seq ?sub (seq ?cof (act fresh))
{-# inline freshIS #-}

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
bindI x act = freshI \i -> BindI x i (act (IVar i))
{-# inline bindI #-}

bindILazy :: Name -> (NCofArg => I -> a) -> (NCofArg => BindILazy a)
bindILazy x act = freshI \i -> BindILazy x i (act (IVar i))
{-# inline bindILazy #-}

bindIS :: Name -> (SubArg => NCofArg => I -> a) -> (SubArg => NCofArg => BindI a)
bindIS x act = freshIS \i -> BindI x i (act (IVar i))
{-# inline bindIS #-}

bindILazyS :: Name -> (SubArg => NCofArg => I -> a) -> (SubArg => NCofArg => BindILazy a)
bindILazyS x act = freshIS \i -> BindILazy x i (act (IVar i))
{-# inline bindILazyS #-}

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
vsempty = VSNe (NSEmpty, mempty)

vscons :: NCofArg => VCof -> (NCofArg => Val) -> VSys -> VSys
vscons cof v ~sys = case cof of
  VCTrue      -> VSTotal v
  VCFalse     -> sys
  VCNe cof is -> case sys of
    VSTotal v'      -> VSTotal v'
    VSNe (sys, is') -> VSNe (NSCons (bindCofLazy cof v) sys // is <> is')
{-# inline vscons #-}

-- | Extend a *neutral* system with a *non-true* cof.
nsconsNonTrue :: NCofArg => VCof -> (NCofArg => Val) -> NeSys -> NeSys
nsconsNonTrue cof v ~sys = case cof of
  VCTrue     -> impossible
  VCFalse    -> sys
  VCNe cof _ -> NSCons (bindCofLazy cof v) sys
{-# inline nsconsNonTrue #-}

-- | Extend a *neutral* system with a *non-true* cof.
nshconsNonTrue' :: NCofArg => VCof -> Name -> (NCofArg => I -> Val) -> NeSysHCom' -> NeSysHCom'
nshconsNonTrue' cof i v (!sys, !is) = case cof of
  VCTrue       -> impossible
  VCFalse      -> (sys, is)
  VCNe cof is' -> NSHCons (bindCof cof (bindILazy i v)) sys // (is <> is')
{-# inline nshconsNonTrue' #-}

evalSys :: SubArg => NCofArg => DomArg => EnvArg => Sys -> VSys
evalSys = \case
  SEmpty          -> vsempty
  SCons cof t sys -> vscons (evalCof cof) (eval t) (evalSys sys)

vshempty :: VSysHCom
vshempty = VSHNe (NSHEmpty, mempty)

vshcons :: NCofArg => VCof -> Name -> (NCofArg => I -> Val) -> VSysHCom -> VSysHCom
vshcons cof i v ~sys = case cof of
  VCTrue       -> VSHTotal (bindILazy i v)
  VCFalse     -> sys
  VCNe cof is -> case sys of
    VSHTotal v'      -> VSHTotal v'
    VSHNe (sys, is') -> VSHNe (NSHCons (bindCof cof (bindILazy i v)) sys // is <> is')
{-# inline vshcons #-}

vshconsS :: SubArg => NCofArg => VCof -> Name -> (SubArg => NCofArg => I -> Val) -> VSysHCom -> VSysHCom
vshconsS cof i v ~sys = case cof of
  VCTrue      -> VSHTotal (bindILazyS i v)
  VCFalse     -> sys
  VCNe cof is -> case sys of
    VSHTotal v'      -> VSHTotal v'
    VSHNe (sys, is') -> VSHNe (NSHCons (bindCof cof (bindILazyS i v)) sys // is <> is')
{-# inline vshconsS #-}

evalSysHCom :: SubArg => NCofArg => DomArg => EnvArg => SysHCom -> VSysHCom
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

vshconsS' :: SubArg => NCofArg => DomArg => EnvArg => VCof -> Name -> Tm -> VSysHCom' -> VSysHCom'
vshconsS' cof i t ~sys = case cof of
  VCTrue      -> VSHTotal' i t
  VCFalse     -> sys
  VCNe cof is -> case sys of
    VSHTotal' x t  -> VSHTotal' x t
    VSHNe' sys is' -> VSHNe' (NSHCons (bindCof cof (bindILazyS i \_ -> eval t)) sys)
                             (is <> is')
{-# inline vshconsS' #-}

evalSysHCom' :: SubArg => NCofArg => DomArg => EnvArg => SysHCom -> VSysHCom'
evalSysHCom' = \case
  SHEmpty            -> vshempty'
  SHCons cof x t sys -> vshconsS' (evalCof cof) x t (evalSysHCom' sys)

hcom' :: SubArg => NCofArg => DomArg => EnvArg => I -> I -> Val -> VSysHCom' -> Val -> Val
hcom' r r' ~a ~t ~b
  | r == r'             = b
  | VSHTotal' x t  <- t = let ?sub = ?sub `ext` r' in eval t
  | VSHNe' nsys is <- t = hcomdn r r' a (nsys, is) b
{-# inline hcom' #-}

com' ::
  SubArg => NCofArg => DomArg => EnvArg => I -> I -> BindI Val -> VSysHCom' -> Val -> Val
com' r r' ~a ~sys ~b
  | r == r'               = b
  | VSHTotal' x t  <- sys = let ?sub = ?sub `ext` r' in eval t
  | VSHNe' nsys is <- sys = hcomdn r r' (a ∙ r')
                              (mapNeSysHCom' (\i t -> coe i r' a t) (nsys,is))
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

mapBindILazy :: NCofArg => SubAction a => BindILazy a -> (NCofArg => I -> a -> b) -> BindILazy b
mapBindILazy t f = bindILazy (t^.name) \i -> f i (t ∙ i)
{-# inline mapBindILazy #-}

-- | Map over a binder in a way which *doesn't* rename the bound variable to a
--   fresh one.  In this case, the mapping function cannot refer to values in
--   external scope, it can only depend on the value under the binder. This can
--   be useful when we only do projections under a binder. The case switch in
--   `coed` on the type argument is similar.
unsafeMapBindI :: NCofArg => BindI a -> (NCofArg => a -> b) -> BindI b
unsafeMapBindI (BindI x i a) f =
  let ?cof = setDomCod (i + 1) i ?cof `ext` IVar i in
  seq ?cof (BindI x i (f a))
{-# inline unsafeMapBindI #-}

unsafeMapBindILazy :: NCofArg => BindILazy a -> (NCofArg => a -> b) -> BindILazy b
unsafeMapBindILazy (BindILazy x i a) f =
  let ?cof = setDomCod (i + 1) i ?cof `ext` IVar i in
  seq ?cof (BindILazy x i (f a))
{-# inline unsafeMapBindILazy #-}

mapNeSys :: NCofArg => (NCofArg => Val -> Val) -> NeSys -> NeSys
mapNeSys f sys = go sys where
  go = \case
    NSEmpty      -> NSEmpty
    NSCons t sys -> NSCons (mapBindCofLazy t f) (go sys)
{-# inline mapNeSys #-}

mapNeSys' :: NCofArg => (NCofArg => Val -> Val) -> NeSys' -> NeSys'
mapNeSys' f (!sys, !is) = (mapNeSys f sys // is)
{-# inline mapNeSys' #-}

mapNeSysHCom :: NCofArg => (NCofArg => I -> Val -> Val) -> NeSysHCom -> NeSysHCom
mapNeSysHCom f sys = go sys where
  go = \case
    NSHEmpty      -> NSHEmpty
    NSHCons t sys -> NSHCons (mapBindCof t \t -> mapBindILazy t f) (go sys)
{-# inline mapNeSysHCom #-}

mapNeSysHCom' :: NCofArg => (NCofArg => I -> Val -> Val) -> NeSysHCom' -> NeSysHCom'
mapNeSysHCom' f (!sys, !is) = (mapNeSysHCom f sys // is)
{-# inline mapNeSysHCom' #-}

mapVSysHCom :: NCofArg => (NCofArg => I -> Val -> Val) -> VSysHCom -> VSysHCom
mapVSysHCom f sys = case sys of
  VSHTotal v      -> VSHTotal (mapBindILazy v f)
  VSHNe (sys, is) -> VSHNe (mapNeSysHCom f sys // is)
{-# inline mapVSysHCom #-}

mapNeSysToH :: NCofArg => (NCofArg => I -> Val -> Val) -> NeSys -> NeSysHCom
mapNeSysToH f sys = case sys of
  NSEmpty      -> NSHEmpty
  NSCons t sys -> NSHCons (bindCof (unBindCofLazy t) (bindILazy "i" \i -> f i (t^.body)))
                          (mapNeSysToH f sys)
{-# inline mapNeSysToH #-}

mapNeSysToH' :: NCofArg => (NCofArg => I -> Val -> Val) -> NeSys' -> NeSysHCom'
mapNeSysToH' f (!sys, !is) = (mapNeSysToH f sys //is)
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
  NSEmpty -> NSHEmpty // mempty
  NSCons t sys ->
    if occursInNeCof (t^.binds) i
      then forallNeSys (BindI x i sys)
      else case forallNeSys (BindI x i sys) of
        (!sys, !is) ->
          NSHCons
            (BindCof (t^.binds) (BindILazy x i (t^.body)))
            sys
         // is <> neCofVars (t^.binds)

-- -- | Map over the (∀i.α) of a system under a binder, returning a NeSysHCom'.
-- --   The BindI in the function arguments refers to the original component value.
-- mapForallNeSys' :: NCofArg => (NCofArg => I -> BindI Val -> Val) -> BindI NeSys -> NeSysHCom'
-- mapForallNeSys' f bind@(BindI x i sys) = case sys of
--   NSEmpty -> NSHEmpty // mempty
--   NSCons t sys ->
--     if occursInNeCof (t^.binds) i
--       then mapForallNeSys' f (BindI x i sys)
--       else case mapForallNeSys' f (BindI x i sys) of
--         (!sys,!is) -> NSHCons (bindCof (unBindCofLazy t)
--                                  (bindILazy x \j -> f j (rebind bind (t^.body))))
--                               sys
--                       // is <> neCofVars (t^.binds)
-- {-# inline mapForallNeSys' #-}

-- System concatenation
----------------------------------------------------------------------------------------------------

catNeSysHCom' :: NeSysHCom' -> NeSysHCom' -> NeSysHCom'
catNeSysHCom' (!sys, !is) (!sys', !is') = catNeSysHCom sys sys' // (is <> is')
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
    VLam t   -> t ∙ u
    VNe t is -> VNe (NApp t u) is
    VTODO    -> VTODO
    _        -> impossible
  {-# inline (∙) #-}

instance Apply (BindI a) I a (SubAction a) NCofArg where
  (∙) (BindI x i a) j =
    let s = setCod i (idSub (dom ?cof)) `ext` j
    in doSub s a
  {-# inline (∙) #-}

instance Apply (BindILazy a) I a (SubAction a) NCofArg where
  (∙) (BindILazy x i a) j =
    let s = setCod i (idSub (dom ?cof)) `ext` j
    in doSub s a
  {-# inline (∙) #-}

instance Apply NamedIClosure I Val NCofArg DomArg where
  (∙) = icapp; {-# inline (∙) #-}

infixl 8 ∙~
(∙~) :: NCofArg => DomArg => Val -> Val -> Val
(∙~) t ~u = case frc t of
  VLam t   -> t ∙ u
  VNe t is -> VNe (NApp t u) is
  VTODO    -> VTODO
  _        -> impossible
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
  CEval (EC s env t) -> let ?env = EDef env u; ?sub = s in eval t

  CCoePi r r' a b t ->
    let ~x = u in
    coe r r' (bindI "j" \j -> b ∙ j ∙ coe r' j a x) (t ∙ coe r' r a x)

  CHComPi r r' a b sys base ->
    hcom r r'
      (b ∙ u)
      (mapVSysHCom (\i t -> t ∙ u) (frc sys))
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
    VPi a $ NCl "a" $ CIsEquiv6 b f g linv rinv

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

  CHInd motive ms t ->
    elim motive ms (t ∙ u)


-- | Apply an ivar closure.
icapp :: NCofArg => DomArg => NamedIClosure -> I -> Val
icapp (NICl _ t) arg = case t of

  ICEval s env t ->
    let ?env = env; ?sub = ext s arg in eval t

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
       mapVSysHCom (\_ t -> papp lhs rhs t j) (frc sys))
      (papp lhs rhs p j)

  -- hcom r r' ((j : A) → B j) [α i. t i] base =
  --   λ j*. hcom
  ICHComLine r r' a sys base ->
    let j = arg in
    hcom r r' (a ∙ j) (mapVSysHCom (\_ t -> lapp t j) (frc sys)) (lapp base j)

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

proj1 :: NCofArg => DomArg => Val -> Val
proj1 t = case frc t of
  VPair t _ -> t
  VNe t is  -> VNe (NProj1 t) is
  VTODO     -> VTODO
  _         -> impossible
{-# inline proj1 #-}

-- | Project under a binder.
proj1BindI :: NCofArg => DomArg => BindI Val -> BindI Val
proj1BindI t = unsafeMapBindI t (\t -> proj1 t)
{-# inline proj1BindI #-}

proj2 :: NCofArg => DomArg => Val -> Val
proj2 t = case frc t of
  VPair _ u -> u
  VNe t is  -> VNe (NProj2 t) is
  VTODO     -> VTODO
  _         -> impossible
{-# inline proj2 #-}

-- | Apply a path.
papp :: NCofArg => DomArg => Val -> Val -> Val -> I -> Val
papp ~l ~r ~t i = case frc i of
  I0     -> l
  I1     -> r
  IVar x -> case frc t of
    VPLam _ _ t -> t ∙ IVar x
    VNe t is    -> VNe (NPApp l r t (IVar x)) (insertIVarF x is)
    VTODO       -> VTODO
    _           -> impossible
{-# inline papp #-}

lapp :: NCofArg => DomArg => Val -> I -> Val
lapp t i = case frc t of
  VLLam t  -> t ∙ i
  VNe t is -> VNe (NLApp t i) is
  VTODO    -> VTODO
  _        -> impossible
{-# inline lapp #-}

-- assumption: r /= r'
coed :: I -> I -> BindI Val -> Val -> NCofArg => DomArg => Val
coed r r' topA t = case (frc topA) ^. body of

  VPi (rebind topA -> a) (rebind topA -> b) ->
    VLam $ NCl (b^.body.name) $ CCoePi r r' a b t

  VSg (rebind topA -> a) (rebind topA -> b) ->
    let t1 = proj1 t
        t2 = proj2 t
    in VPair (coed r r' a t1)
             (coed r r' (bindI "j" \j -> coe r j a t1) t2)

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

  VTyCon x (rebind topA -> ps) ->
    uf

  -- Note: I don't need to rebind the "is"! It can be immediately weakened
  -- to the outer context.
  n@(VNe _ is) ->
    VNe (NCoe r r' (rebind topA n) t) (insertI r $ insertI r' is)

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

  VGlueTy (rebind topA -> a) (rebind topA -> topSys, rebind topA -> is) -> let

    gr           = t
    ~_Ar'        = a ∙ r'
    ~topSysr     = topSys ∙ r :: NeSys
    ~topSysrf    = frc topSysr
    ~topSysr'    = topSys ∙ r' :: NeSys
    topSysr'f    = frc topSysr'
    forallTopSys = forallNeSys topSys

  -- ar' : Ar'
  -- ar' := comp r r' (i. A i) [(∀i.α) i. f i (coe r i (j. T j) gr)] (unglue gr sysr)

    ~ar' =
          hcomdn r r' _Ar'
             (mapNeSysHCom'
                (\i tf -> coe i r' a (proj1 (proj2 (tf ∙ i)) ∙ coe r i (proj1BindI tf) gr))
                forallTopSys)
             (coed r r' a (unglue gr topSysrf))

    mkComponent :: NCofArg => Val -> (Val, BindILazy Val)
    mkComponent tfr' = let

      ~equiv1  = tfr'
      ~equiv2  = proj2 equiv1
      ~equiv3  = proj2 equiv2
      ~equiv4  = proj2 equiv3
      ~equiv5  = proj2 equiv4

      ~tr'     = proj1 equiv1
      ~fr'     = proj1 equiv2
      ~fr'inv  = proj1 equiv3
      ~r'linv  = proj1 equiv4
      ~r'rinv  = proj1 equiv5
      ~r'coh   = proj2 equiv5

      ~fibval  = fr'inv ∙ ar'
      ~fibpath = r'rinv ∙ ar'

      -- shorthands for path applications
      app_r'linv :: NCofArg => Val -> I -> Val
      app_r'linv ~x i =
        papp x (fr'inv ∙ fr' ∙ x) (r'linv ∙ x) i

      app_r'coh :: NCofArg => Val -> I -> I -> Val
      app_r'coh ~x i j =
        papp (fr' ∙ app_r'linv x i)
             (fr' ∙ x)
             (papp (refl (fr' ∙ x)) (r'rinv ∙ (fr' ∙ x)) (r'coh ∙ x) i)
             j

      -- valSys should be fine without NCof polymorphism

      -- valSys = [r=r'  i. fr'.linv gr i
      --         ;(∀i.α) i. fr'.linv (coe r r' (i. T i) gr) i]
      ~valSys = uf
        -- nshconsNonTrue' (ceq r r') "i" (\i -> app_r'linv gr i) $
        -- mapForallNeSys' (\i tf -> app_r'linv (coe r r' (proj1BindI tf) gr) i) topSys

      -- fibval* : Tr'
      -- fibval* = hcom 1 0 Tr' valSys fibval
      ~fibval' = hcomdn I1 I0 tr' valSys fibval

      -- fibpath* : fr' fibval = ar'
      -- fibpath* = λ j.
      --    hcom 1 0 (A r') [j=0    i. fr' (hcom 1 i Tr' valSys fibval)    -- no need to force valSys because
      --                    ;j=1    i. ar'                                 -- it's independent from j=0
      --                    ;r=r'   i. fr'.coh gr i
      --                    ;(∀i.α) i. fr'.coh (coe r r' (i. T i) gr) i]
      --                    (fibpath {fr' fibval} {ar'} j)

      fibpath' = uf
        -- bindILazy "i" \j ->
        -- hcomd I1 I0 _Ar'
        --   (vshcons (ceq j I0) "i" (\i -> fr' ∙ hcomn I1 i tr' valSys fibval) $
        --    vshcons (ceq j I1) "i" (\i -> ar') $
        --    VSHNe $
        --    nshconsNonTrue' (ceq r r') "i" (\i -> app_r'coh gr i j) $
        --    mapForallNeSys' (\i tf -> app_r'coh (coe r r' (proj1BindI tf) gr) i j) topSys
        --   )
        --   (papp (fr' ∙ fibval) ar' fibpath j)

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
      VSNe (sys, is) -> let
        (!fibvals, !fibpaths) = mkNeSystems sys
        in VSNe (fibvals, is) // VSHNe (fibpaths, is)

    in glue
         (hcomd I1 I0 _Ar' (vshcons (ceq r r') "i" (\i -> unglue gr (frc topSysr)) fibpaths) ar')
         topSysr'f
         fibvals

  _ ->
    impossible


coe :: NCofArg => DomArg => I -> I -> BindI Val -> Val -> Val
coe r r' ~a t
  | frc r == frc r' = t
  | True            = coed r r' a t
{-# inline coe #-}

-- | HCom with off-diagonal I args ("d") and neutral system arg ("n").
hcomdn :: I -> I -> Val -> NeSysHCom' -> Val -> NCofArg => DomArg => Val
hcomdn r r' topA ts@(!nts, !is) base = case frc topA of
  VPi a b ->
    VLam $ NCl (b^.name) $ CHComPi r r' a b nts base

  VSg a b ->
    let bbind :: NCofArg => BindI Val
        bbind = seq ?cof $
         bindI "i" \i ->
          b ∙ hcomn r i a
               (mapNeSysHCom' (\_ t -> proj1 t) ts)
               (proj1 base) in
    VPair
      (hcomdn r r' a
        (mapNeSysHCom' (\_ t -> proj1 t) ts)
        (proj1 base))
      (hcomdn r r'
        (b ∙ hcomn r r' a
             (mapNeSysHCom' (\_ t -> proj1 t) ts)
             (proj1 base))
        (mapNeSysHCom' (\i t -> coe i r' bbind (proj2 t)) ts)
        (coed r r' bbind (proj2 base)))

  -- (  hcom r r' A [α i. (t i).1] b.1
  --  , com r r' (i. B (hcom r i A [α j. (t j).1] b.1)) [α i. (t i).2] b.2)

  VPath a lhs rhs ->
        VPLam lhs rhs
      $ NICl (a^.name)
      $ ICHComPath r r' a lhs rhs nts base

  a@(VNe n is') ->
        VNe (NHCom r r' a nts base)
            (insertI r $ insertI r' $ is <> is')

  -- hcom r r' U [α i. t i] b =
  --   Glue b [r=r'. (b, idEquiv); α. (t r', (coe r' r (i. t i), coeIsEquiv))]

  VU -> let

    -- NOTE the nsconsNonTrue; ceq r r' can be false or neutral
    sys = nsconsNonTrue (ceq r r') (VPair base (theIdEquiv base)) $
          mapNeSysFromH
            (\t -> VPair (t ∙ r') (theCoeEquiv (bindI (t^.name) \i -> t ∙ i) r' r))
            nts

    in VGlueTy base (sys // (insertI r $ insertI r' is))

-- hcom for Glue
--------------------------------------------------------------------------------

  -- hcom r r' (Glue [α. (T, f)] A) [β i. t i] gr =
  --   glue (hcom r r' A [β i. unglue (t i); α i. f (hcom r i T [β. t] gr)] (unglue gr))
  --        [α. hcom r r' T [β i. t i] gr]

  VGlueTy a (alphasys, alphais) ->
    let gr         = base
        alphasys'  = (alphasys, alphais)
        betasys    = nts
        betais     = is
        betasys'   = (betasys, betais)

            -- [α. hcom r r' T [β i. t i] gr]
        fib = mapNeSys (\t -> hcomd r r' (proj1 t) (frc betasys) gr) alphasys

        -- hcom r r' A [  β i. unglue (t i)
        --              ; α i. f (hcom r i T [β. t] gr)]
        --             (unglue gr)
        hcombase =
          hcomdn r r' a
            (catNeSysHCom'
               (mapNeSysHCom' (\_ t -> unglue t (frc alphasys)) betasys')
               (mapNeSysToH'
                  (\i tf ->
                      let ty  = proj1 tf             -- T
                          f   = proj1 (proj2 tf) in  -- f
                      f ∙ hcomd r i ty (frc betasys) gr)
                  alphasys'))
            (unglue gr (frc alphasys))

    in VNe (NGlue hcombase alphasys fib) (insertI r $ insertI r' (alphais <> betais))

  VLine a ->
        VLLam
      $ NICl (a^.name)
      $ ICHComLine r r' a nts base

  a@(VTyCon x ps) -> case base of
    VDCon x i sp     -> case ?dom of
                          0 -> hcomind0 r r a ts ps x i sp
                          _ -> hcomind  r r a ts ps x i sp
    base@(VNe n is') -> VNe (NHCom r r' a nts base)
                            (insertI r $ insertI r' $ is <> is')
    VTODO            -> VTODO
    _                -> impossible

  a ->
    error $ show a


----------------------------------------------------------------------------------------------------

-- | HCom with nothing known about semantic arguments.
hcom :: NCofArg => DomArg => I -> I -> Val -> VSysHCom -> Val -> Val
hcom r r' ~a ~t ~b
  | frc r == frc r' = b
  | True = case t of
      VSHTotal v -> v ∙ r'
      VSHNe sys  -> hcomdn r r' a sys b
{-# inline hcom #-}

-- hcom
-- hcomf
-- hcomd
-- hcomdf
-- hcomdnf

-- coe
-- coed
-- coenf
-- coednf

-- | HCom with neutral system input.
hcomn :: NCofArg => DomArg => I -> I -> Val -> NeSysHCom' -> Val -> Val
hcomn r r' ~a ~sys ~b
  | r == r' = b
  | True    = hcomdn r r' a sys b
{-# inline hcomn #-}

-- | Off-diagonal HCom.
hcomd :: NCofArg => DomArg => I -> I -> Val -> VSysHCom -> Val -> Val
hcomd r r' ~a ~sys ~b = case sys of
  VSHTotal v -> v ∙ r'
  VSHNe sys  -> hcomdn r r' a sys b
{-# inline hcomd #-}

glueTy :: NCofArg => DomArg => Val -> VSys -> Val
glueTy ~a sys = case sys of
  VSTotal b -> proj1 b
  VSNe sys  -> VGlueTy a sys
{-# inline glueTy #-}

glueTyNoinline :: NCofArg => DomArg => Val -> VSys -> Val
glueTyNoinline ~a sys = case sys of
  VSTotal b -> proj1 b
  VSNe sys  -> VGlueTy a sys
{-# noinline glueTyNoinline #-}

glue :: Val -> VSys -> VSys -> Val
glue ~t eqs sys = case (eqs, sys) of
  (VSTotal{}    , VSTotal v)      -> v
  (VSNe (eqs, _), VSNe (sys, is)) -> VNe (NGlue t eqs sys) is
  _                               -> impossible
{-# inline glue #-}

unglue :: NCofArg => DomArg => Val -> VSys -> Val
unglue ~t sys = case sys of
  VSTotal teqv   -> proj1 (proj2 teqv) ∙ t
  VSNe (sys, is) -> case frc t of
    VNe n is' -> case unSubNe n of
      NGlue base _ _ -> base
      n              -> VNe (NUnglue n sys) (is <> is')
    _ -> impossible
{-# inline unglue #-}

-- | Unglue with neutral system arg.
ungluen :: NCofArg => DomArg => Val -> NeSys' -> Val
ungluen t (!sys, !is) = case frc t of
  VNe n is' -> case unSubNe n of
    NGlue base _ _ -> base
    n              -> VNe (NUnglue n sys) (is <> is')
  _ -> impossible
{-# inline ungluen #-}


-- Strict inductive types
----------------------------------------------------------------------------------------------------


tyParams :: SubArg => NCofArg => DomArg => EnvArg => TyParams -> Env
tyParams TPNil         = ENil
tyParams (TPSnoc as a) = EDef (tyParams as) (eval a)

dSpine :: SubArg => NCofArg => DomArg => EnvArg => DSpine -> VDSpine
dSpine = \case
  DNil         -> VDNil
  DInd t sp    -> VDInd (eval t) (dSpine sp)
  DHInd t a sp -> VDHInd (eval t) a (dSpine sp)
  DExt t a sp  -> VDExt (eval t) a (dSpine sp)

methods :: SubArg => EnvArg => Methods -> VMethods
methods = \case
  MNil          -> VMNil
  MCons xs t ms -> VMCons xs (EC ?sub ?env t) (methods ms)

evalMethod :: SubArg => NCofArg => DomArg => EnvArg => Val -> VMethods -> VDSpine -> Tm -> Val
evalMethod ~motive ms sp body = case sp of
  VDNil         -> eval body
  VDInd t sp    -> let ~elimt = elim motive ms (frc t) in
                   let ?env = ?env `EDef` t `EDef` elimt in
                   evalMethod motive ms sp body
  VDHInd t _ sp -> let elimt = VLam (NCl "x" (CHInd motive ms t)) in
                   let ?env = ?env `EDef` t `EDef` elimt in
                   evalMethod motive ms sp body
  VDExt t _ sp  -> let ?env = ?env `EDef` t in evalMethod motive ms sp body

lookupMethod :: NCofArg => DomArg => Lvl -> Val -> VMethods -> VDSpine -> Val
lookupMethod i ~motive ms sp = case (i, ms) of
  (0, VMCons xs (EC sub env t) _) -> let ?sub = sub; ?env = env in evalMethod motive ms sp t
  (i, VMCons _ _ ms             ) -> lookupMethod (i - 1) motive ms sp
  _                               -> impossible

elim :: NCofArg => DomArg => Val -> VMethods -> Val -> Val
elim ~motive ms val = case frc val of
  VDCon _ i sp -> lookupMethod i motive ms sp
  VNe n is     -> VNe (NElim motive ms n) is
  VTODO        -> VTODO
  _            -> impossible
{-# inline elim #-}

projsp :: NCofArg => DomArg => Lvl -> VDSpine -> Val
projsp ix sp = case (ix, sp) of
  (0 , VDInd t _     ) -> t
  (0 , VDHInd t _ _  ) -> t
  (0 , VDExt t _ _   ) -> t
  (ix, VDInd _ sp    ) -> projsp (ix - 1) sp
  (ix, VDHInd _ _ sp ) -> projsp (ix - 1) sp
  (ix, VDExt _ _ sp  ) -> projsp (ix - 1) sp
  _                    -> impossible

lazyprojfield :: NCofArg => DomArg => Lvl -> Lvl -> Val -> Val
lazyprojfield conix fieldix v = case frc v of
  VDCon x i sp | i == conix -> projsp fieldix sp
  _                         -> impossible
{-# inline lazyprojfield #-}

-- Project all fieldix fields of a constructor conix from a system
lazyprojsys :: NCofArg => DomArg => Lvl -> Lvl -> NeSysHCom -> NeSysHCom
lazyprojsys conix fieldix = \case
  NSHEmpty      -> NSHEmpty
  NSHCons t sys -> NSHCons (mapBindCof t \t -> unsafeMapBindILazy t (lazyprojfield conix fieldix))
                           (lazyprojsys conix fieldix sys)

lazyprojsys' :: NCofArg => DomArg => Lvl -> Lvl -> NeSysHCom' -> NeSysHCom'
lazyprojsys' conix fieldix (!sys, !is) = (lazyprojsys conix fieldix sys // is)
{-# inline lazyprojsys' #-}

hcomind0sp :: NCofArg => DomArg => I -> I -> Val -> NeSysHCom' -> Env -> Lvl -> Lvl -> VDSpine -> VDSpine
hcomind0sp r r' topa sys ext conix fieldix sp = case sp of
  VDNil ->
    VDNil
  VDInd t sp ->
    VDInd (hcomdn r r' topa (lazyprojsys' conix fieldix sys) (frc t))
          (hcomind0sp r r' topa sys ext conix (fieldix + 1) sp)
  VDHInd t a sp ->
    let va = (let ?env = ext; ?sub = idSub (dom ?cof) in eval a) in
    VDHInd (hcomdn r r' (funf va topa) (lazyprojsys' conix fieldix sys) t)
           a
           (hcomind0sp r r' topa sys (EDef ext t) conix (fieldix + 1) sp)
  VDExt t a sp  ->
    let ~va = (let ?env = ext; ?sub = idSub (dom ?cof) in eval a) in
    VDExt (hcomdn r r' va (lazyprojsys' conix fieldix sys) t)
          a
          (hcomind0sp r r' topa sys (EDef ext t) conix (fieldix + 1) sp)

hcomind0 :: NCofArg => DomArg => I -> I -> Val -> NeSysHCom' -> Env -> Lvl -> Lvl -> VDSpine -> Val
hcomind0 r r' a sys ext tyix conix sp =
  VDCon tyix conix (hcomind0sp r r' a sys ext conix 0 sp)
{-# inline hcomind0 #-}


-- System where all components are known to be the same constructor
data Projected
  = PNil
  | PCons NeCof Name IVar VDSpine Projected

type Projected' = (Projected, IVarSet)

-- TODO: unbox
data TryToProject
  = TTPProject Projected
  | TTPNe {-# unpack #-} NeSysHCom'

projsys :: NCofArg => DomArg => Lvl -> NeSysHCom' -> NeSysHCom -> TryToProject
projsys conix topSys@(!_,!_) = \case
  NSHEmpty      -> TTPProject PNil
  NSHCons t sys ->
    let ~prj = projsys conix topSys sys; {-# inline prj #-} in

    assumeCof (t^.binds) $ case (frc (t^.body))^.body of
      VDCon _ conix' sp | conix == conix' ->
        case prj of
          TTPProject prj ->
            TTPProject (PCons (t^.binds) (t^.body.name) (t^.body.binds) sp prj)
          prj@TTPNe{} ->
            prj

      VNe n is -> TTPNe (fst topSys // is <> snd topSys) -- extend blockers with is'
      _        -> impossible

projsys' :: NCofArg => DomArg => Lvl -> NeSysHCom' -> TryToProject
projsys' conix (!sys, !is) = projsys conix (sys, is) sys
{-# inline projsys' #-}

projfields :: Projected -> Lvl -> NeSysHCom
projfields prj fieldix = case prj of
  PNil ->
    NSHEmpty
  PCons ncof x i sp prj ->
    NSHCons (BindCof ncof (BindILazy x i uf)) (projfields prj fieldix)

projfields' :: Projected' -> Lvl ->NeSysHCom'
projfields' (!prj,!is) fieldix = (projfields prj fieldix // is)
{-# inline projfields' #-}

hcomindsp :: NCofArg => DomArg => I -> I -> Val -> Projected' -> Env -> Lvl -> Lvl -> VDSpine -> VDSpine
hcomindsp r r' topa prj@(!_,!_) ext conix fieldix sp = case sp of
  VDNil ->
    VDNil
  VDInd t sp ->
    VDInd (hcomdn r r' topa (projfields' prj fieldix) (frc t))
          (hcomindsp r r' topa prj ext conix (fieldix + 1) sp)
  VDHInd t a sp ->
    let va = (let ?env = ext; ?sub = idSub (dom ?cof) in eval a) in
    VDHInd (hcomdn r r' (funf va topa) (projfields' prj fieldix) t)
           a
           (hcomindsp r r' topa prj (EDef ext t) conix (fieldix + 1) sp)

  VDExt t a sp  ->
    let ~va = (let ?env = ext; ?sub = idSub (dom ?cof) in eval a) in
    VDExt (hcomdn r r' va (projfields' prj fieldix) t)
          a
          (hcomindsp r r' topa prj (EDef ext t) conix (fieldix + 1) sp)

hcomind :: NCofArg => DomArg => I -> I -> Val -> NeSysHCom' -> Env -> Lvl -> Lvl -> VDSpine -> Val
hcomind r r' a sys ext tyix conix sp = case projsys' conix sys of
  TTPProject prj ->
    VDCon tyix conix (hcomindsp r r' a (prj // snd sys) ext conix 0 sp)
  TTPNe (sys,is) ->
    VNe (NHCom r r' a sys (VDCon tyix conix sp)) (insertI r $ insertI r' is)
{-# inline hcomind #-}

-- coeind :: NCofArg => DomArg => F I -> F I ->


----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

eval :: SubArg => NCofArg => DomArg => EnvArg => Tm -> Val
eval = \case

  TopVar _ v        -> coerce v
  LocalVar x        -> localVar x
  Let x _ t u       -> define (eval t) (eval u)

  -- Pi
  Pi x a b          -> VPi (eval a) (NCl x (CEval (EC ?sub ?env b)))
  App t u           -> eval t ∙ eval u
  Lam x t           -> VLam (NCl x (CEval (EC ?sub ?env t)))

  -- Sigma
  Sg x a b          -> VSg (eval a) (NCl x (CEval (EC ?sub ?env b)))
  Pair t u          -> VPair (eval t) (eval u)
  Proj1 t           -> proj1 (eval t)
  Proj2 t           -> proj2 (eval t)

  -- U
  U                 -> VU

  -- Path
  Path x a t u      -> VPath (NICl x (ICEval ?sub ?env a)) (eval t) (eval u)
  PApp l r t i      -> papp (eval l) (eval r) (eval t) (evalI i)
  PLam l r x t      -> VPLam (eval l) (eval r) (NICl x (ICEval ?sub ?env t))

  -- Kan
  Coe r r' x a t    -> coe   (evalI r) (evalI r') (bindIS x \_ -> eval a) (eval t)
  HCom r r' a t b   -> hcom' (evalI r) (evalI r') (eval a) (evalSysHCom' t) (eval b)

  -- Glue
  GlueTy a sys      -> glueTy (eval a) (evalSys sys)
  Glue t eqs sys    -> glue   (eval t) (evalSys eqs) (evalSys sys)
  Unglue t sys      -> unglue (eval t) (evalSys sys)

  -- Line
  Line x a          -> VLine (NICl x (ICEval ?sub ?env a))
  LApp t i          -> lapp (eval t) (evalI i)
  LLam x t          -> VLLam (NICl x (ICEval ?sub ?env t))

  -- Misc
  WkI _ t           -> wkIS (eval t)
  TODO              -> VTODO

  -- Builtins
  Refl t            -> refl (eval t)
  Sym a x y p       -> sym (eval a) (eval x) (eval y) (eval p)
  Trans a x y z p q -> trans (eval a) (eval x) (eval y) (eval z) (eval p) (eval q)
  Ap f x y p        -> ap_ (eval f) (eval x) (eval y) (eval p)
  Com r r' i a t b  -> com' (evalI r) (evalI r') (bindIS i \_ -> eval a) (evalSysHCom' t) (eval b)

  -- Inductives
  TyCon x ts        -> VTyCon x (tyParams ts)
  DCon x i sp       -> VDCon x i (dSpine sp)
  Elim mot met t    -> elim (eval mot) (methods met) (eval t)


----------------------------------------------------------------------------------------------------
-- Forcing
----------------------------------------------------------------------------------------------------

class Force a b | a -> b where
  frc  :: NCofArg => DomArg => a -> b           -- force a value wrt current cof. Idempotent.
  frcS :: SubArg => NCofArg => DomArg => a -> b -- apply a substitution and then force. *Not* idempotent!
                                                -- Applying it multiple times is an error.

instance Force I I where
  frc  i = doSub ?cof i;              {-# inline frc #-}
  frcS i = doSub ?cof (doSub ?sub i); {-# inline frcS #-}

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

recFrc :: NCofArg => DomArg => Val -> Val
recFrc = \case
  VSub v s                             -> let ?sub = s in frcS v
  VNe t is            | isUnblocked is -> frc t
  VGlueTy a (sys, is) | isUnblocked is -> recFrc (glueTyNoinline a (frc sys))
  v                                    -> v

instance Force Val Val where
  frc = \case
    VSub v s                             -> let ?sub = s in frcS v
    VNe t is            | isUnblocked is -> frc t
    VGlueTy a (sys, is) | isUnblocked is -> recFrc (glueTyNoinline a (frc sys))
    v                                    -> v
  {-# inline frc #-}

  frcS = \case
    VSub v s                              -> let ?sub = sub s in frcS v
    VNe t is            | isUnblockedS is -> frcS t
    VGlueTy a (sys, is) | isUnblockedS is -> recFrc (glueTy (sub a) (frcS sys))

    VNe t is      -> VNe (sub t) (sub is)
    VGlueTy a sys -> VGlueTy (sub a) (sub sys)
    VPi a b       -> VPi (sub a) (sub b)
    VLam t        -> VLam (sub t)
    VPath a t u   -> VPath (sub a) (sub t) (sub u)
    VPLam l r t   -> VPLam (sub l) (sub r) (sub t)
    VSg a b       -> VSg (sub a) (sub b)
    VPair t u     -> VPair (sub t) (sub u)
    VU            -> VU
    VTODO         -> VTODO
    VLine t       -> VLine (sub t)
    VLLam t       -> VLLam (sub t)
    VTyCon x ts   -> VTyCon x (sub ts)
    VDCon x i sp  -> VDCon x i (sub sp)
  {-# noinline frcS #-}

instance Force Ne Val where
  frc = \case
    t@NLocalVar{}     -> VNe t mempty
    NSub n s          -> let ?sub = s in frcS n
    NApp t u          -> recFrc (frc t ∙ u)
    NPApp l r t i     -> recFrc (papp l r (frc t) i)
    NProj1 t          -> recFrc (proj1 (frc t))
    NProj2 t          -> recFrc (proj2 (frc t))
    NCoe r r' a t     -> recFrc (coe r r' (frc a) (frc t))
    NHCom r r' a ts t -> recFrc (hcom r r' (frc a) (frc ts) t)
    NUnglue t sys     -> recFrc (unglue (frc t) (frc sys))
    NGlue t eqs sys   -> recFrc (glue t (frc eqs) (frc sys))
    NLApp t i         -> recFrc (lapp (frc t) i)
    NElim mot ms t    -> recFrc (elim mot ms (frc t))
  {-# noinline frc #-}

  frcS = \case
    t@NLocalVar{}     -> VNe t mempty
    NSub n s          -> let ?sub = sub s in frcS n
    NApp t u          -> recFrc (frcS t ∙ sub u)
    NPApp l r t i     -> recFrc (papp (sub l) (sub r) (frcS t) (frcS i))
    NProj1 t          -> recFrc (proj1 (frcS t))
    NProj2 t          -> recFrc (proj2 (frcS t))
    NCoe r r' a t     -> recFrc (coe (frcS r) (frcS r') (frcS a) (frcS t))
    NHCom r r' a ts t -> recFrc (hcom (frcS r) (frcS r') (frcS a) (frcS ts) (frcS t))
    NUnglue t sys     -> recFrc (unglue (frcS t) (frcS sys))
    NGlue t eqs sys   -> recFrc (glue (sub t) (frcS eqs) (frcS sys))
    NLApp t i         -> recFrc (lapp (frcS t) (frcS i))
    NElim mot ms t    -> recFrc (elim (sub mot) (sub ms) (frcS t))

instance Force NeSys VSys where
  -- TODO: is it better to not do anything with system components in frc?
  -- The current version can pile up frc thunks. They're very cheap though,
  -- expect for the first one.

  frc = \case
    NSEmpty      -> vsempty
    NSCons t sys -> vscons (frc (t^.binds)) (frc (t^.body)) (frc sys)

  frcS = \case
    NSEmpty      -> vsempty
    NSCons t sys -> vscons (frcS (t^.binds)) (frcS (t^.body)) (frc sys)

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
        VSHTotal v'      -> VSHTotal v'
        VSHNe (sys, is') -> VSHNe (NSHCons (bindCof cof (t^.body)) sys // is <> is')

  frcS = \case
    NSHEmpty ->
      vshempty
    NSHCons t sys -> case frcS (t^.binds) of
      VCTrue      -> VSHTotal (frcS (t^.body))
      VCFalse     -> frcS sys
      VCNe cof is -> case frcS sys of
        VSHTotal v'      -> VSHTotal v'
        VSHNe (sys, is') -> VSHNe (NSHCons (bindCof cof (frcS (t^.body))) sys // is <> is')

instance Force a fa => Force (BindI a) (BindI fa) where

  frc (BindI x i a) =
    let ?cof = setDomCod (i + 1) i ?cof `ext` IVar i in
    seq ?cof (BindI x i (frc a))
  {-# inline frc #-}

  frcS (BindI x i a) =
    let fresh = dom ?cof in
    let ?sub  = setCod i ?sub `ext` IVar fresh in
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
    let ?sub  = setCod i ?sub `ext` IVar fresh in
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
  NApp t u           -> NApp (sub t) (sub u)
  NPApp l r p i      -> NPApp (sub l) (sub r) (sub p) (sub i)
  NProj1 t           -> NProj1 (sub t)
  NProj2 t           -> NProj2 (sub t)
  NCoe r r' a t      -> NCoe (sub r) (sub r') (sub a) (sub t)
  NHCom r r' a sys t -> NHCom (sub r) (sub r') (sub a) (sub sys) (sub t)
  NUnglue a sys      -> NUnglue (sub a) (sub sys)
  NGlue a eqs sys    -> NGlue (sub a) (sub eqs) (sub sys)
  NLApp t i          -> NLApp (sub t) (sub i)
  NElim mot ms t     -> NElim (sub mot) (sub ms) (sub t)

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
equiv a b = VSg (fun a b) $ NCl "g" $ CEquiv a b

-- | U -> U
equivInto :: Val -> Val
equivInto a = VSg VU $ NCl "b" $ CEquivInto a

-- | idIsEquiv : (A : U) -> isEquiv (\(x:A).x)
idIsEquiv :: Val -> Val
idIsEquiv a =
  VPair (VLam $ NCl "a" C'λ'a''a) $
  VPair (VLam $ NCl "a" C'λ'a'i''a) $
  VPair (VLam $ NCl "b" C'λ'a'i''a) $
        (VLam $ NCl "a" C'λ'a'i'j''a)

-- | Identity function packed together with isEquiv.
theIdEquiv :: Val -> Val
theIdEquiv a =
  VPair (VLam $ NCl "x" C'λ'a''a)
        (idIsEquiv a)


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
  VPair (VLam $ NCl "x" $ CCoeAlong a r' r) $
  VPair (VLam $ NCl "x" $ CCoeLinv0 a r r') $
  VPair (VLam $ NCl "x" $ CCoeRinv0 a r r') $
        (VLam $ NCl "x" $ CCoeCoh0  a r r')

-- | Coercion function packed together with isEquiv.
theCoeEquiv :: BindI Val -> I -> I -> Val
theCoeEquiv a r r' =
  VPair (VLam $ NCl "x" $ CCoeAlong a r r')
        (coeIsEquiv a r r')
