
module Core where

import qualified IVarSet as IS
import Common
import Interval
import Substitution
import CoreTypes

import Debug.Trace


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

assumeCof :: NeCof -> (NCofArg => a) -> (NCofArg => a)
assumeCof cof act = let ?cof = conjNeCof ?cof cof in seq ?cof act
{-# inline assumeCof #-}

wkIS :: (SubArg => NCofArg => a) -> (SubArg => NCofArg => a)
wkIS act =
  let cod' = cod ?sub - 1 in
  let ?sub = setCod cod' ?sub in
  let ?cof = setCod cod' ?cof in
  let _ = ?sub; _ = ?cof in
  act
{-# inline wkIS #-}

----------------------------------------------------------------------------------------------------
-- Creating semantic binders
----------------------------------------------------------------------------------------------------


bindCof :: NeCof -> (NCofArg => a) -> (NCofArg => BindCof a)
bindCof cof act = assumeCof cof (BindCof cof act)
{-# inline bindCof #-}

bindCoff :: NeCof -> (NCofArg => F a) -> (NCofArg => F (BindCof a))
bindCoff cof act = assumeCof cof (F (BindCof cof (unF act)))
{-# inline bindCoff #-}

bindCofLazy :: NeCof -> (NCofArg => F a) -> (NCofArg => F (BindCofLazy a))
bindCofLazy cof act = assumeCof cof (F (BindCofLazy cof (unF act)))
{-# inline bindCofLazy #-}

bindCofLazynf :: NeCof -> (NCofArg => F a) -> (NCofArg => BindCofLazy a)
bindCofLazynf cof act = unF (bindCofLazy cof act)
{-# inline bindCofLazynf #-}

bindI :: Name -> (NCofArg => F I -> a) -> (NCofArg => BindI a)
bindI x act = freshI \i -> BindI x i (act (F (IVar i)))
{-# inline bindI #-}

bindIf :: Name -> (NCofArg => F I -> F a) -> (NCofArg => F (BindI a))
bindIf x act = freshI \i -> F (BindI x i (unF (act (F (IVar i)))))
{-# inline bindIf #-}

bindILazy :: Name -> (NCofArg => F I -> F a) -> (NCofArg => F (BindILazy a))
bindILazy x act = freshI \i -> F (BindILazy x i (unF (act (F (IVar i)))))
{-# inline bindILazy #-}

bindILazynf :: Name -> (NCofArg => F I -> F a) -> (NCofArg => BindILazy a)
bindILazynf x act = unF (bindILazy x act)
{-# inline bindILazynf #-}

bindIS :: Name -> (SubArg => NCofArg => F I -> F a) -> (SubArg => NCofArg => F (BindI a))
bindIS x act = freshIS \i -> F (BindI x i (unF (act (F (IVar i)))))
{-# inline bindIS #-}

bindILazyS :: Name -> (SubArg => NCofArg => F I -> F a) -> (SubArg => NCofArg => F (BindILazy a))
bindILazyS x act = freshIS \i -> F (BindILazy x i (unF (act (F (IVar i)))))
{-# inline bindILazyS #-}

bindILazySnf :: Name -> (SubArg => NCofArg => F I -> F a) -> (SubArg => NCofArg => BindILazy a)
bindILazySnf x act = unF (bindILazyS x act)
{-# inline bindILazySnf #-}


----------------------------------------------------------------------------------------------------
-- Cof and Sys semantics
----------------------------------------------------------------------------------------------------

ctrue, cfalse :: F VCof
ctrue  = F VCTrue
cfalse = F VCFalse

cand :: F VCof -> F VCof -> F VCof
cand c1 ~c2 = case (unF c1, unF c2) of
  (VCFalse    , c2         ) -> cfalse
  (_          , VCFalse    ) -> cfalse
  (VCTrue     , c2         ) -> F c2
  (c1         , VCTrue     ) -> F c1
  (VCNe n1 is1, VCNe n2 is2) -> F (VCNe (NCAnd n1 n2) (is1 <> is2))
{-# inline cand #-}

ceq :: F I -> F I -> F VCof
ceq c1 c2 = case (unF c1, unF c2) of
  (i, j) | i == j -> ctrue
  (i, j) -> matchIVar i
    (\x -> matchIVar j
      (\y -> F (VCNe (NCEq i j) (IS.singleton x <> IS.singleton y)))
      (F (VCNe (NCEq i j) (IS.singleton x))))
    (matchIVar j
      (\y -> F (VCNe (NCEq i j) (IS.singleton y)))
      cfalse)

evalI :: SubArg => NCofArg => I -> F I
evalI i = F (doSub ?cof (doSub ?sub i))

evalCofEq :: SubArg => NCofArg => CofEq -> F VCof
evalCofEq (CofEq i j) = ceq (evalI i) (evalI j)

evalCof :: SubArg => NCofArg => Cof -> F VCof
evalCof = \case
  CTrue       -> ctrue
  CAnd eq cof -> cand (evalCofEq eq) (evalCof cof)

conjIVarI :: NCof -> IVar -> I -> NCof
conjIVarI cof x i = mapSub id go cof where
  go _ j = matchIVar j (\y -> if x == y then i else j) j

conjNeCof :: NCof -> NeCof -> NCof
conjNeCof ncof necof = case necof of
  NCAnd c1 c2 -> ncof `conjNeCof` c1 `conjNeCof` c2
  NCEq i j    -> case (i, j) of
    (IVar x, IVar y) -> let (!x', !i') = if x > y then (x, IVar y)
                                                  else (y, IVar x) in
                        conjIVarI ncof x' i'
    (IVar x, j     ) -> conjIVarI ncof x j
    (i     , IVar y) -> conjIVarI ncof y i
    (i     , j     ) -> error $ show (i, j)

conjVCof :: NCof -> F VCof -> NCof
conjVCof ncof cof = case unF cof of
  VCFalse      -> impossible
  VCTrue       -> ncof
  VCNe necof _ -> conjNeCof ncof necof
{-# inline conjVCof #-}

vsempty :: F VSys
vsempty = F (VSNe NSEmpty mempty)
{-# inline vsempty #-}

vscons :: NCofArg => F VCof -> (NCofArg => F Val) -> F VSys -> F VSys
vscons cof v ~sys = case unF cof of
  VCTrue      -> F (VSTotal (unF v))
  VCFalse     -> sys
  VCNe cof is -> case unF sys of
    VSTotal v'   -> F (VSTotal v')
    VSNe sys is' -> F (VSNe (NSCons (bindCofLazynf cof v) sys) (is <> is'))
{-# inline vscons #-}

-- | Extend a *neutral* system with a *non-true* cof.
nsconsNonTrue :: NCofArg => F VCof -> (NCofArg => F Val) -> F NeSys -> F NeSys
nsconsNonTrue cof v ~sys = case unF cof of
  VCTrue      -> impossible
  VCFalse     -> sys
  VCNe cof is -> F (NSCons (bindCofLazynf cof v) (unF sys))
{-# inline nsconsNonTrue #-}

evalSys :: SubArg => NCofArg => DomArg => EnvArg => Sys -> F VSys
evalSys = \case
  SEmpty          -> vsempty
  SCons cof t sys -> vscons (evalCof cof) (evalf t) (evalSys sys)

vshempty :: F VSysHCom
vshempty = F (VSHNe NSHEmpty mempty)
{-# inline vshempty #-}

vshcons :: NCofArg => F VCof -> Name -> (NCofArg => F I -> F Val) -> F VSysHCom -> F VSysHCom
vshcons cof i v ~sys = case unF cof of
  VCTrue      -> F (VSHTotal (unF (bindILazy i v)))
  VCFalse     -> sys
  VCNe cof is -> case unF sys of
    VSHTotal v'   -> F (VSHTotal v')
    VSHNe sys is' -> F (VSHNe (NSHCons (bindCof cof (bindILazynf i v)) sys) (is <> is'))
{-# inline vshcons #-}

vshconsS :: SubArg => NCofArg => F VCof -> Name -> (SubArg => NCofArg => F I -> F Val)
         -> F VSysHCom -> F VSysHCom
vshconsS cof i v ~sys = case unF cof of
  VCTrue      -> F (VSHTotal (bindILazySnf i v))
  VCFalse     -> sys
  VCNe cof is -> case unF sys of
    VSHTotal v'   -> F (VSHTotal v')
    VSHNe sys is' -> F (VSHNe (NSHCons (bindCof cof (bindILazySnf i v)) sys) (is <> is'))
{-# inline vshconsS #-}

evalSysHCom :: SubArg => NCofArg => DomArg => EnvArg => SysHCom -> F VSysHCom
evalSysHCom = \case
  SHEmpty            -> vshempty
  SHCons cof x t sys -> vshconsS (evalCof cof) x (\_ -> evalf t) (evalSysHCom sys)


----------------------------------------------------------------------------------------------------
-- Mapping
----------------------------------------------------------------------------------------------------

mapBindCof :: NCofArg => BindCof a -> (NCofArg => a -> a) -> BindCof a
mapBindCof t f = bindCof (t^.binds) (f (t^.body))
{-# inline mapBindCof #-}

mapBindCofLazy :: NCofArg => BindCofLazy a -> (NCofArg => a -> F a) -> F (BindCofLazy a)
mapBindCofLazy t f = bindCofLazy (t^.binds) (f (t^.body))
{-# inline mapBindCofLazy #-}

mapBindCofLazynf :: NCofArg => BindCofLazy a -> (NCofArg => a -> F a) -> BindCofLazy a
mapBindCofLazynf t f = unF (mapBindCofLazy t f)
{-# inline mapBindCofLazynf #-}

mapBindILazy :: NCofArg => BindILazy Val -> (NCofArg => F I -> Val -> F Val) -> F (BindILazy Val)
mapBindILazy t f = bindILazy (t^.name) \i -> f i (t ∙ unF i)
{-# inline mapBindILazy #-}

mapBindILazynf :: NCofArg => BindILazy Val -> (NCofArg => F I -> Val -> F Val) -> BindILazy Val
mapBindILazynf t f = unF (mapBindILazy t f); {-# inline mapBindILazynf #-}

mapNeSys :: NCofArg => (NCofArg => Val -> F Val) -> F NeSys -> F NeSys
mapNeSys f sys = F (go (unF sys)) where
  go :: NeSys -> NeSys
  go = \case
    NSEmpty      -> NSEmpty
    NSCons t sys -> NSCons (mapBindCofLazynf t f) (go sys)
{-# inline mapNeSys #-}

mapNeSysHCom :: NCofArg => (NCofArg => F I -> Val -> F Val) -> F NeSysHCom -> F NeSysHCom
mapNeSysHCom f sys = F (go (unF sys)) where
  go :: NeSysHCom -> NeSysHCom
  go = \case
    NSHEmpty      -> NSHEmpty
    NSHCons t sys -> NSHCons (mapBindCof t \t -> mapBindILazynf t f) (go sys)
{-# inline mapNeSysHCom #-}

mapNeSysHComnf :: NCofArg => (NCofArg => F I -> Val -> F Val) -> F NeSysHCom -> NeSysHCom
mapNeSysHComnf f sys = unF (mapNeSysHCom f sys); {-# inline mapNeSysHComnf #-}

mapNeSysHCom' :: NCofArg => (NCofArg => F I -> Val -> F Val)
              -> F (NeSysHCom, IS.IVarSet)
              -> F (NeSysHCom, IS.IVarSet)
mapNeSysHCom' f (F (sys, is)) = F (mapNeSysHComnf f (F sys), is)
{-# inline mapNeSysHCom' #-}

mapVSysHCom :: NCofArg => (NCofArg => F I -> Val -> F Val) -> F VSysHCom -> F VSysHCom
mapVSysHCom f sys = case unF sys of
  VSHTotal v   -> F (VSHTotal (mapBindILazynf v f))
  VSHNe sys is -> F (VSHNe (mapNeSysHComnf f (F sys)) is)
{-# inline mapVSysHCom #-}

----------------------------------------------------------------------------------------------------
-- Overloaded application and forcing
----------------------------------------------------------------------------------------------------

infixl 8 ∙
class Apply a b c a1 a2 | a -> b c a1 a2 where
  (∙) :: a1 => a2 => a -> b -> c

instance Apply NamedClosure Val Val NCofArg DomArg where
  (∙) = capp; {-# inline (∙) #-}

instance Apply (F Val) Val Val NCofArg DomArg where
  (∙) t u = case unF t of
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

infixl 8 ∘
class ApplyF a b c a1 a2 a3 | a -> b c a1 a2 a3 where
  (∘) :: a1 => a2 => a3 => a -> b -> F c

instance ApplyF NamedClosure Val Val NCofArg DomArg () where
  (∘) x ~y = frc (x ∙ y); {-# inline (∘) #-}

instance ApplyF (F Val) Val Val NCofArg DomArg () where
  (∘) x y = frc (x ∙ y); {-# inline (∘) #-}

instance Force a fa => ApplyF (BindI a) I fa (SubAction a) NCofArg DomArg where
  (∘) x y = frc (x ∙ y); {-# inline (∘) #-}

instance Force a fa => ApplyF (BindILazy a) I fa (SubAction a) NCofArg DomArg where
  (∘) x y = frc (x ∙ y); {-# inline (∘) #-}

instance ApplyF NamedIClosure I Val NCofArg DomArg () where
  (∘) x y = frc (x ∙ y); {-# inline (∘) #-}

infixl 8 ∙~
(∙~) :: NCofArg => DomArg => F Val -> Val -> Val
(∙~) t ~u = case unF t of
  VLam t   -> t ∙ u
  VNe t is -> VNe (NApp t u) is
  VTODO    -> VTODO
  _        -> impossible


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
  CEval s env t -> let ?env = EDef env u; ?sub = s in eval t

  CCoePi (frc -> r) (frc -> r') (frc -> a) b (frc -> t) ->
    let x = frc u in
    coenf r r' (bindIf "j" \j -> b ∙ unF j ∘ coenf r' j a x) (t ∘ coenf r' r a x)

  CHComPi (frc -> r) (frc -> r') a b sys base ->
    hcom r r'
      (b ∘ u)
      (mapVSysHCom (\i t -> frc t ∘ u) (frc sys))
      (frc base ∘ u)

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
    VSg (VPi a $ NCl "a" $ CIsEquiv4 a f g) $ NCl "linv" $ CIsEquiv2 a b f g

  CIsEquiv2 a b f g -> let ~linv = u in
    VSg (VPi a $ NCl "a" $ CIsEquiv5 b f g) $ NCl "rinv" $ CIsEquiv3 a b f g linv

  CIsEquiv3 a b f g linv -> let ~rinv = u in
    VPi a $ NCl "a" $ CIsEquiv6 b f g linv rinv

  CIsEquiv4 a (frc -> f) (frc -> g) -> let ~x = u in path a x (g ∙ (f ∙ x))
  CIsEquiv5 b (frc -> f) (frc -> g) -> let ~x = u in path b (f ∙ (g ∙ x)) x

  CIsEquiv6 b (frc -> f) g linv (frc -> rinv) ->
    let ~x  = u
        ~fx = f ∙ x in
    VPath (NICl "i" $ ICIsEquiv7 b (unF f) g linv x)
      (refl fx)
      (rinv ∙ fx)

  ------------------------------------------------------------

  -- equiv A B = (f* : A -> B) × isEquiv a b f
  CEquiv a b -> let ~f = u in isEquiv a b f

  -- [P]  (n* : VNat) → P n → P (suc n)
  CNatElim (frc -> p) -> let ~n = u in fun (p ∙ n) (p ∙ VSuc n)

  -- [A]  (B* : U) × equiv B A
  CEquivInto a -> let ~b = u in equiv a b

  -- ------------------------------------------------------------

  C'λ'a''a     -> u
  C'λ'a'i''a   -> refl u
  C'λ'a'i'j''a -> let ru = refl u in VPLam ru ru $ NICl "i" $ ICConst ru

  -- coeIsEquiv : (Γ, i ⊢ A : U) (r r' : I) → Γ ⊢ isEquiv (coeⁱ r r' A : Ar → Ar')
  -- coeIsEquiv A r r' =
  --   _⁻¹  := λ x^1. coeⁱ r' r A x
  --   linv := λ x^0. λ j^1. hcom r r' (A r)  [j=0 k. x; j=1 k. coeⁱ k r A (coeⁱ r k A x)] x
  --   rinv := λ x^0. λ j^1. hcom r' r (A r') [j=0 k. coeⁱ k r' A (coeⁱ r' k A x); j=1 k. x] x
  --   coh  := TODO

  CCoeAlong (frc -> a) (frc -> r) (frc -> r') ->
    let ~x = u in coenf r r' a (frc x)

  CCoeLinv0 (frc -> a) (frc -> r) (frc -> r') ->
    let ~x   = frc u
        -- x = g (f x)
        ~lhs = unF x
        ~rhs = coenf r' r a (coe r r' a x)
    in VPLam lhs rhs $ NICl "j" $ ICCoeLinv1 (unF a) (unF x) (unF r) (unF r')

  CCoeRinv0 (frc -> a) (frc -> r) (frc -> r') ->
    let ~x   = frc u
        -- f (g x) = x
        ~lhs = coenf r r' a (coe r' r a x)
        ~rhs = unF x
    in VPLam lhs rhs $ NICl "j" $ ICCoeRinv1 (unF a) (unF x) (unF r) (unF r')

-- | Apply a Path closure.
icapp :: NCofArg => DomArg => NamedIClosure -> I -> Val
icapp (NICl _ t) arg = case t of
  ICEval s env t ->
    let ?env = env; ?sub = ext s arg in eval t

  ICCoePath (frc -> r) (frc -> r') a lhs rhs p ->
    let j = frc arg in
    com r r' (bindIf "i" \i -> a ∙ unF i ∘ unF j)
             (vshcons (ceq j fi0) "i" (\i -> lhs ∘ unF i) $
              vshcons (ceq j fi1) "i" (\i -> rhs ∘ unF i) $
              vshempty)
             (pappf (lhs ∙ unF r') (rhs ∙ unF r') (frc p) j)

  ICHComPath (frc -> r) (frc -> r') a lhs rhs sys p ->
    let farg = frc arg in
    hcom r r' (a ∘ unF farg)
      (vshcons (ceq farg fi0) "i" (\i -> frc lhs) $
       vshcons (ceq farg fi1) "i" (\i -> frc rhs) $
       mapVSysHCom (\_ t -> pappf lhs rhs (frc t) farg) (frc sys))
      (pappf lhs rhs (frc p) farg)

  ICHComLine (frc -> r) (frc -> r') a sys base ->
    let farg = frc arg in
    hcom r r' (a ∘ unF farg)
      (mapVSysHCom (\_ t -> lappf (frc t) farg) (frc sys))
      (lappf (frc base) farg)

  ICCoeLine (frc -> r) (frc -> r') a p ->
    let j = frc arg in
    coednf r r' (bindIf "i" \i -> a ∙ unF i ∘ unF j)
                (lappf (frc p) j)

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

  ICIsEquiv7 b (frc -> f) (frc -> g)(frc -> linv) x ->
    let ~i   = frc arg
        ~fx  = f ∙ x
        ~gfx = g ∙ fx  in
    path b (f ∙ papp x gfx (linv ∘ x) i) fx

  -- coeIsEquiv : (Γ, i ⊢ A : U) (r r' : I) → Γ ⊢ isEquiv (coeⁱ r r' A : Ar → Ar')
  -- coeIsEquiv A r r' =
  --   _⁻¹  := λ x^1. coeⁱ r' r A x
  --   linv := λ x^0. λ j^1. hcom r r' (A r)  [j=0 k. x; j=1 k. coeⁱ k r A (coeⁱ r k A x)] x
  --   rinv := λ x^0. λ j^1. hcom r' r (A r') [j=0 k. coeⁱ k r' A (coeⁱ r' k A x); j=1 k. x] x
  --   coh  := TODO

  ICCoeLinv1 (frc -> a) (frc -> x) (frc -> r) (frc -> r') ->
    let j = frc arg in
    hcom r r'
      (unF a ∘ unF r)
      (vshcons (ceq j fi0) "k" (\_ -> x) $
       vshcons (ceq j fi1) "k" (\k -> coe k r a (coe r k a x)) $
       vshempty)
      x

  ICCoeRinv1 (frc -> a) (frc -> x) (frc -> r) (frc -> r') ->
    let j = frc arg in
    hcom r' r
      (unF a ∘ unF r')
      (vshcons (ceq j fi0) "k" (\k -> coe k r' a (coe r' k a x)) $
       vshcons (ceq j fi1) "k" (\_ -> x) $
       vshempty)
      x


proj1 :: F Val -> Val
proj1 t = case unF t of
  VPair t _ -> t
  VNe t is  -> VNe (NProj1 t) is
  VTODO     -> VTODO
  _         -> impossible
{-# inline proj1 #-}

proj1f t = frc (proj1 t); {-# inline proj1f  #-}

proj2 :: F Val -> Val
proj2 t = case unF t of
  VPair _ u -> u
  VNe t is  -> VNe (NProj2 t) is
  VTODO     -> VTODO
  _         -> impossible
{-# inline proj2 #-}

proj2f t = frc (proj2 t); {-# inline proj2f #-}

natElim :: NCofArg => DomArg => Val -> Val -> F Val -> F Val -> Val
natElim p z s n = case unF n of
  VZero           -> z
  VSuc (frc -> n) -> s ∘ unF n ∙ natElim p z s n
  VNe n is        -> VNe (NNatElim p z (unF s) n) is
  VTODO           -> VTODO
  _               -> impossible

natElimf p z s n = frc (natElim p z s n); {-# inline natElimf #-}

-- | Apply a path.
papp :: NCofArg => DomArg => Val -> Val -> F Val -> F I -> Val
papp ~l ~r ~t i = case unF i of
  I0     -> l
  I1     -> r
  IVar x -> case unF t of
    VPLam _ _ t -> t ∙ IVar x
    VNe t is    -> VNe (NPApp l r t (IVar x)) (IS.insert x is)
    VTODO       -> VTODO
    _           -> impossible
{-# inline papp #-}

pappf ~t ~u0 ~u1 i = frc (papp t u0 u1 i); {-# inline pappf #-}

lapp :: NCofArg => DomArg => F Val -> F I -> Val
lapp t i = case unF t of
  VLLam t  -> t ∙ unF i
  VNe t is -> VNe (NLApp t (unF i)) is
  VTODO    -> VTODO
  _        -> impossible
{-# inline lapp #-}

lappf t i = frc (lapp t i); {-# inline lappf #-}

-- assumption: r /= r'
coed :: F I -> F I -> F (BindI Val) -> F Val -> NCofArg => DomArg => F Val
coed r r' topA t = case unF topA ^. body of

  VPi (rebind topA -> a) (rebind topA -> b) ->
    F (VLam (NCl (b^.body.name) (CCoePi (unF r) (unF r') a b (unF t))))

  VSg (rebindf topA -> a) (rebindf topA -> b) ->
    let t1 = proj1f t
        t2 = proj2f t
    in F (VPair (coednf r r' a t1)
                (coednf r r' (bindIf "j" \j -> coe r j a t1) t2))

  VNat ->
    t

  VPath (rebind topA -> a) (rebind topA -> lhs) (rebind topA -> rhs) ->
    F $ VPLam (lhs ∙ unF r') (rhs ∙ unF r')
      $ NICl (a^.body.name)
      $ ICCoePath (unF r) (unF r') a lhs rhs (unF t)

  VLine (rebind topA -> a) ->
    F $ VLLam
      $ NICl (a^.body.name)
      $ ICCoeLine (unF r) (unF r') a (unF t)

  VU ->
    t

  -- Note: I don't need to rebind the "is"! It can be immediately weakened
  -- to the outer context.
  VNe (rebind topA -> n) is ->
    F (VNe (NCoe (unF r) (unF r') (unF topA) (unF t))
           (IS.insertI (unF r) $ IS.insertI (unF r') is))

  VGlueTy a sys is ->
    F VTODO

  _ ->
    impossible

coednf r r' a t = unF (coed r r' a t); {-# inline coednf #-}

coe :: NCofArg => DomArg => F I -> F I -> F (BindI Val) -> F Val -> F Val
coe r r' ~a t
  | r == r' = t
  | True    = coed r r' a t
{-# inline coe #-}

coenf r r' a t = unF (coe r r' a t); {-# inline coenf #-}

-- | Assumption: r /= r'
comdn :: NCofArg => DomArg => F I -> F I -> F (BindI Val) -> F (NeSysHCom, IS.IVarSet) -> F Val -> F Val
comdn r r' ~a sys ~b =
  hcomdn r r'
    (unF a ∘ unF r')
    (mapNeSysHCom' (\i t -> coe i r' a (frc t)) sys)
    (coed r r' a b)
{-# noinline comdn #-}

comdnnf r r' ~a sys ~b = unF (comdn r r' a sys b); {-# inline comdnnf #-}

com :: NCofArg => DomArg => F I -> F I -> F (BindI Val) -> F VSysHCom -> F Val -> Val
com r r' ~a ~sys ~b
  | r == r'                  = unF b
  | VSHTotal v    <- unF sys = v ∙ unF r'
  | VSHNe nsys is <- unF sys = comdnnf r r' a (F (nsys, is)) b
{-# inline com #-}

-- projZero :: NCofArg => DomArg => F I -> F I -> F NeSysHCom -> F Val
-- projZero r r' sys = case unF sys of

-- projSuc :: NCofArg => DomArg => F I -> F I -> F NeSysHCom -> F Val -> F Val
-- projSuc = uf

-- -- | HCom Nat with off-diagonal I args ("d") and neutral system arg ("n").
-- hcomNatdn :: NCofArg => DomArg => F I -> F I -> F NeSysHCom -> F Val -> F Val
-- hcomNatdn r r' sys base = case unF base of
--   VZero  -> projZero r r' sys
--   VSuc n -> hcomNatdn r r'

-- | HCom with off-diagonal I args ("d") and neutral system arg ("n").
hcomdn :: F I -> F I -> F Val -> F (NeSysHCom, IS.IVarSet) -> F Val -> NCofArg => DomArg => F Val
hcomdn r r' a ts@(F (!nts, !is)) base = case unF a of

  VPi a b ->
    F $ VLam $ NCl (b^.name) $ CHComPi (unF r) (unF r') a b nts (unF base)

  VSg a b ->
    F $ VPair
      (hcomdnnf r r'
        (frc a)
        (mapNeSysHCom' (\_ t -> proj1f (frc t)) ts)
        (proj1f base))
      (comdnnf r r'
        (bindIf "i" \i ->
          hcomn r i
            (frc a)
            (mapNeSysHCom' (\_ t -> proj1f (frc t)) ts)
            (proj1f base))
        (mapNeSysHCom' (\_ t -> proj2f (frc t)) ts)
        (proj2f base))

  VNat -> case ?dom of
    0 -> base
    _ -> F VTODO -- hcomNatdn r r' (F nts) base

  VPath a lhs rhs ->
    F $ VPLam lhs rhs
      $ NICl (a^.name)
      $ ICHComPath (unF r) (unF r') a lhs rhs nts (unF base)

  a@(VNe n is') ->
    F $ VNe (NHCom (unF r) (unF r') a nts (unF base))
            (IS.insertFI r $ IS.insertFI r' $ is <> is')

-- hcom r r' U [α i. ↦ t] b = Glue [α ↦ (t r', (coeⁱ r' r (t i), coeIsEquiv)), r=r' ↦ (b, idEqv)] b
  VU -> let
    is' = IS.insertI (unF r) $ IS.insertI (unF r') is

    mkSys :: NCofArg => F I -> F I -> NeSysHCom -> NeSys
    mkSys r r' sys = seq ?cof $ case sys of
      NSHEmpty -> NSEmpty
      NSHCons t sys ->
        NSCons (bindCofLazynf (t^.binds) $
                  F $ VPair (t^.body ∙ unF r')
                    $ theCoeEquiv (bindI (t^.body.name) \i -> t^.body ∙ unF i)
                                  (unF r') (unF r))
               (mkSys r r' sys)

    -- NOTE the nsconsNonTrue; ceq r r' can be false or neutral
    sys = nsconsNonTrue (ceq r r') (F (theIdEquiv (unF base))) (F (mkSys r r' nts))
    in F $ VGlueTy (unF base) (unF sys) is'


  VGlueTy a sys is' ->
    F VTODO

  VLine a ->
    F $ VLLam
      $ NICl (a^.name)
      $ ICHComLine (unF r) (unF r') a nts (unF base)

  _ ->
    impossible

-- | HCom with nothing known about semantic arguments.
hcom :: NCofArg => DomArg => F I -> F I -> F Val -> F VSysHCom -> F Val -> Val
hcom r r' ~a ~t ~b
  | r == r'                = unF b
  | VSHTotal v    <- unF t = v ∙ unF r'
  | VSHNe nsys is <- unF t = hcomdnnf r r' a (F (nsys, is)) b
{-# inline hcom #-}

-- | HCom with neutral system input.
hcomn :: NCofArg => DomArg => F I -> F I -> F Val -> F (NeSysHCom, IS.IVarSet) -> F Val -> F Val
hcomn r r' ~a ~sys ~b
  | r == r' = b
  | True    = hcomdn r r' a sys b
{-# inline hcomn #-}

hcomdnnf r r' a sys base = unF (hcomdn r r' a sys base); {-# inline hcomdnnf #-}
hcomf r r' ~a ~t ~b = frc (hcom r r' a t b); {-# inline hcomf  #-}

glueTy :: NCofArg => DomArg => Val -> F VSys -> Val
glueTy a sys = case unF sys of
  VSTotal b   -> proj1 (frc b)
  VSNe sys is -> VGlueTy a sys is
{-# inline glueTy #-}

glueTyf a sys = frc (glueTy a sys); {-# inline glueTyf #-}

glue :: Val -> F VSys -> Val
glue t sys = case unF sys of
  VSTotal v   -> v
  VSNe sys is -> VNe (NGlue t sys) is
{-# inline glue #-}

gluef t sys = frc (glue t sys); {-# inline gluef #-}

unglue :: NCofArg => DomArg => Val -> F VSys -> Val
unglue t sys = case unF sys of
  VSTotal teqv -> proj1f (proj2f (frc teqv)) ∙ t
  VSNe sys is  -> VNe (NUnglue t sys) is
{-# inline unglue #-}

ungluef t sys = frc (unglue t sys); {-# inline ungluef #-}

eval :: SubArg => NCofArg => DomArg => EnvArg => Tm -> Val
eval = \case
  TopVar _ v       -> coerce v
  LocalVar x       -> localVar x
  Let x _ t u      -> define (eval t) (eval u)
  Pi x a b         -> VPi (eval a) (NCl x (CEval ?sub ?env b))
  App t u          -> evalf t ∙ eval u
  Lam x t          -> VLam (NCl x (CEval ?sub ?env t))
  Sg x a b         -> VSg (eval a) (NCl x (CEval ?sub ?env b))
  Pair t u         -> VPair (eval t) (eval u)
  Proj1 t          -> proj1 (evalf t)
  Proj2 t          -> proj2 (evalf t)
  U                -> VU
  Path x a t u     -> VPath (NICl x (ICEval ?sub ?env a)) (eval t) (eval u)
  PApp l r t i     -> papp (eval l) (eval r) (evalf t) (evalI i)
  PLam l r x t     -> VPLam (eval l) (eval r) (NICl x (ICEval ?sub ?env t))
  Coe r r' x a t   -> coenf (evalI r) (evalI r') (bindIS x \_ -> evalf a) (evalf t)
  HCom r r' a t b  -> hcom (evalI r) (evalI r') (evalf a) (evalSysHCom t) (evalf b)
  GlueTy a sys     -> glueTy (eval a) (evalSys sys)
  Glue t sys       -> glue (eval t) (evalSys sys)
  Unglue t sys     -> unglue (eval t) (evalSys sys)
  Nat              -> VNat
  Zero             -> VZero
  Suc t            -> VSuc (eval t)
  NatElim p z s n  -> natElim (eval p) (eval z) (evalf s) (evalf n)
  TODO             -> VTODO
  Com r r' i a t b -> com (evalI r) (evalI r') (bindIS i \_ -> evalf a) (evalSysHCom t) (evalf b)
  Line x a         -> VLine (NICl x (ICEval ?sub ?env a))
  LApp t i         -> lapp (evalf t) (evalI i)
  LLam x t         -> VLLam (NICl x (ICEval ?sub ?env t))
  WkI _ t          -> wkIS (eval t)

evalf :: SubArg => NCofArg => DomArg => EnvArg => Tm -> F Val
evalf t = frc (eval t)
{-# inline evalf #-}


----------------------------------------------------------------------------------------------------
-- Forcing
----------------------------------------------------------------------------------------------------

class Force a b | a -> b where
  frc  :: NCofArg => DomArg => a -> F b           -- force a value wrt current cof
  frcS :: SubArg => NCofArg => DomArg => a -> F b -- apply a substitution and then force

instance Force I I where
  frc  i = F (doSub ?cof i); {-# inline frc #-}
  frcS i = F (doSub ?cof (doSub ?sub i)); {-# inline frcS #-}

instance Force NeCof VCof where
  frc = \case
    NCEq i j    -> ceq (frc i) (frc j)
    NCAnd c1 c2 -> cand (frc c1) (frc c2)

  frcS = \case
    NCEq i j    -> ceq (frcS i) (frcS j)
    NCAnd c1 c2 -> cand (frcS c1) (frcS c2)

instance Force Val Val where
  frc = \case
    VSub v s                          -> let ?sub = s in frcS v
    VNe t is         | isUnblocked is -> frc t
    VGlueTy a sys is | isUnblocked is -> glueTyf a (frc sys)
    v                                 -> F v

  frcS = \case
    VSub v s                           -> let ?sub = sub s in frcS v
    VNe t is         | isUnblockedS is -> frcS t
    VGlueTy a sys is | isUnblockedS is -> glueTyf (sub a) (frcS sys)

    VNe t is          -> F (VNe (sub t) (sub is))
    VGlueTy a sys is  -> F (VGlueTy (sub a) (sub sys) (sub is))
    VPi a b           -> F (VPi (sub a) (sub b))
    VLam t            -> F (VLam (sub t))
    VPath a t u       -> F (VPath (sub a) (sub t) (sub u))
    VPLam l r t       -> F (VPLam (sub l) (sub r) (sub t))
    VSg a b           -> F (VSg (sub a) (sub b))
    VPair t u         -> F (VPair (sub t) (sub u))
    VU                -> F VU
    VNat              -> F VNat
    VZero             -> F VZero
    VSuc t            -> F (VSuc (sub t))
    VTODO             -> F VTODO
    VLine t           -> F (VLine (sub t))
    VLLam t           -> F (VLLam (sub t))

instance Force Ne Val where
  frc = \case
    t@NLocalVar{}     -> F (VNe t mempty)
    NSub n s          -> let ?sub = s in frcS n
    NApp t u          -> frc t ∘ u
    NPApp l r t i     -> pappf l r (frc t) (frc i)
    NProj1 t          -> proj1f (frc t)
    NProj2 t          -> proj2f (frc t)
    NCoe r r' a t     -> coe (frc r) (frc r') (frc a) (frc t)
    NHCom r r' a ts t -> hcomf (frc r) (frc r') (frc a) (frc ts) (frc t)
    NUnglue t sys     -> ungluef t (frc sys)
    NGlue t sys       -> gluef t (frc sys)
    NNatElim p z s n  -> natElimf p z (frc s) (frc n)
    NLApp t i         -> lappf (frc t) (frc i)

  frcS = \case
    t@NLocalVar{}     -> F (VNe t mempty)
    NSub n s          -> let ?sub = sub s in frcS n
    NApp t u          -> frcS t ∘ sub u
    NPApp l r t i     -> pappf (sub l) (sub r) (frcS t) (frcS i)
    NProj1 t          -> proj1f (frcS t)
    NProj2 t          -> proj2f (frcS t)
    NCoe r r' a t     -> coe (frcS r) (frcS r') (frcS a) (frcS t)
    NHCom r r' a ts t -> hcomf (frcS r) (frcS r') (frcS a) (frcS ts) (frcS t)
    NUnglue t sys     -> ungluef (sub t) (frcS sys)
    NGlue t sys       -> gluef (sub t) (frcS sys)
    NNatElim p z s n  -> natElimf (sub p) (sub z) (frcS s) (frcS n)
    NLApp t i         -> lappf (frcS t) (frcS i)

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
  -- Definitions are more unrolled and optimized here.
  -- The semantic vshcons operations always rename the bound vars to the current
  -- fresh var. The optimized "frc" here makes it possible to frc without any
  -- substitution.
  -- TODO: is it better to not do anything with components in frc?

  frc = \case
    NSHEmpty ->
      vshempty
    NSHCons t sys -> case unF (frc (t^.binds)) of
      VCTrue      -> F (VSHTotal (unF (frc (t^.body))))
      VCFalse     -> frc sys
      VCNe cof is -> case unF (frc sys) of
        VSHTotal v'   -> F (VSHTotal v')
        VSHNe sys is' -> F (VSHNe (NSHCons (bindCof cof (unF (frc (t^.body)))) sys) (is <> is'))

  frcS = \case
    NSHEmpty ->
      vshempty
    NSHCons t sys -> case unF (frcS (t^.binds)) of
      VCTrue      -> F (VSHTotal (unF (frcS (t^.body))))
      VCFalse     -> frcS sys
      VCNe cof is -> case unF (frcS sys) of
        VSHTotal v'   -> F (VSHTotal v')
        VSHNe sys is' -> F (VSHNe (NSHCons (bindCof cof (unF (frcS (t^.body)))) sys) (is <> is'))

instance Force a fa => Force (BindI a) (BindI fa) where

  frc (BindI x i a) =
    let ?cof = setDomCod (i + 1) i ?cof `ext` IVar i in
    seq ?cof (F (BindI x i (unF (frc a))))
  {-# inline frc #-}

  frcS (BindI x i a) =
    let fresh = dom ?cof in
    let ?sub  = setCod i ?sub `ext` IVar fresh in
    let ?cof  = setDom (fresh+1) ?cof `ext` IVar fresh in
    seq ?sub $ seq ?cof $ F (BindI x fresh (unF (frcS a)))
  {-# inline frcS #-}

instance Force a fa => Force (BindILazy a) (BindILazy fa) where

  frc (BindILazy x i a) =
    let ?cof = setDomCod (i + 1) i ?cof `ext` IVar i in
    seq ?cof (F (BindILazy x i (unF (frc a))))
  {-# inline frc #-}

  frcS (BindILazy x i a) =
    let fresh = dom ?cof in
    let ?sub  = setCod i ?sub `ext` IVar fresh in
    let ?cof  = setDom (fresh+1) ?cof `ext` IVar fresh in
    seq ?sub $ seq ?cof $ F (BindILazy x fresh (unF (frcS a)))
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
  NSub n s             -> let ?sub = sub s in unSubNeS n
  NLocalVar x          -> NLocalVar x
  NApp t u             -> NApp (sub t) (sub u)
  NPApp l r p i        -> NPApp (sub l) (sub r) (sub p) (sub i)
  NProj1 t             -> NProj1 (sub t)
  NProj2 t             -> NProj2 (sub t)
  NCoe r r' a t        -> NCoe (sub r) (sub r') (sub a) (sub t)
  NHCom r r' a sys t   -> NHCom (sub r) (sub r') (sub a) (sub sys) (sub t)
  NUnglue a sys        -> NUnglue (sub a) (sub sys)
  NGlue a sys          -> NGlue (sub a) (sub sys)
  NNatElim p z s n     -> NNatElim (sub p) (sub z) (sub s) (sub n)
  NLApp t i            -> NLApp (sub t) (sub i)

----------------------------------------------------------------------------------------------------
-- Definitions
----------------------------------------------------------------------------------------------------

fun :: Val -> Val -> Val
fun a b = VPi a $ NCl "_" $ CConst b

-- | (A : U) -> A -> A -> U
path :: Val -> Val -> Val -> Val
path a t u = VPath (NICl "_" (ICConst a)) t u

-- | (x : A) -> PathP _ x x
refl :: Val -> Val
refl t = VPLam t t $ NICl "_" $ ICConst t

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

coeIsEquiv :: BindI Val -> I -> I -> Val
coeIsEquiv a r r' =
  VPair (VLam $ NCl "x" $ CCoeAlong a r' r) $
  VPair (VLam $ NCl "x" $ CCoeLinv0 a r r') $
  VPair (VLam $ NCl "x" $ CCoeRinv0 a r r') $
        VTODO

-- | Coercion function packed together with isEquiv.
theCoeEquiv :: BindI Val -> I -> I -> Val
theCoeEquiv a r r' =
  VPair (VLam $ NCl "x" $ CCoeAlong a r r')
        (coeIsEquiv a r r')
