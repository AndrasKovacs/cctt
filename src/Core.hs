
module Core where

import qualified IVarSet as IS
import Common
import Interval
import Substitution
import CoreTypes

-- import Pretty
-- import Debug.Trace


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

bindCoff :: NeCof' -> (NCofArg => F a) -> (NCofArg => F (BindCof a))
bindCoff (NeCof' cof c) act = let ?cof = cof in F (BindCof c (unF act))
{-# inline bindCoff #-}

bindCofLazy :: NeCof' -> (NCofArg => F a) -> (NCofArg => F (BindCofLazy a))
bindCofLazy (NeCof' cof c) act = let ?cof = cof in F (BindCofLazy c (unF act))
{-# inline bindCofLazy #-}

bindCofLazynf :: NeCof' -> (NCofArg => F a) -> (NCofArg => BindCofLazy a)
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

vcne :: NCofArg => NeCof -> IS.IVarSet -> VCof
vcne nc is = VCNe (NeCof' (conjNeCof ?cof nc) nc) is

ceq :: NCofArg => F I -> F I -> F VCof
ceq c1 c2 = case (unF c1, unF c2) of
  (i, j) | i == j -> ctrue
  (i, j) -> matchIVar i
    (\x -> matchIVar j
      (\y -> F (vcne (NCEq i j) (IS.singleton x <> IS.singleton y)))
      (F (vcne (NCEq i j) (IS.singleton x))))
    (matchIVar j
      (\y -> F (vcne (NCEq i j) (IS.singleton y)))
      cfalse)

evalI :: SubArg => NCofArg => I -> F I
evalI i = F (doSub ?cof (doSub ?sub i))

evalCofEq :: SubArg => NCofArg => CofEq -> F VCof
evalCofEq (CofEq i j) = ceq (evalI i) (evalI j)

evalCof :: SubArg => NCofArg => Cof -> F VCof
evalCof = \case
  CTrue       -> ctrue
  CAnd eq cof -> case unF (evalCofEq eq) of
    VCTrue      -> evalCof cof
    VCFalse     -> cfalse
    VCNe c is -> let ?cof = c^.extended in case unF (evalCof cof) of
      VCTrue      -> F $ VCNe c is
      VCFalse     -> cfalse
      VCNe c' is' -> F $ VCNe (NeCof' (c^.extended) (NCAnd (c^.extra) (c'^.extra)))
                              (is <> is')

vsempty :: F VSys
vsempty = F (VSNe (NSEmpty, mempty))

vscons :: NCofArg => F VCof -> (NCofArg => F Val) -> F VSys -> F VSys
vscons cof v ~sys = case unF cof of
  VCTrue      -> F (VSTotal v)
  VCFalse     -> sys
  VCNe cof is -> case unF sys of
    VSTotal v'      -> F $ VSTotal v'
    VSNe (sys, is') -> F $ VSNe (NSCons (bindCofLazynf cof v) sys // is <> is')
{-# inline vscons #-}

-- | Extend a *neutral* system with a *non-true* cof.
nsconsNonTrue :: NCofArg => F VCof -> (NCofArg => F Val) -> F NeSys -> F NeSys
nsconsNonTrue cof v ~sys = case unF cof of
  VCTrue     -> impossible
  VCFalse    -> sys
  VCNe cof _ -> F $ NSCons (bindCofLazynf cof v) (unF sys)
{-# inline nsconsNonTrue #-}

-- | Extend a *neutral* system with a *non-true* cof.
nshconsNonTrue' :: NCofArg => F VCof -> Name -> (NCofArg => F I -> F Val) -> F NeSysHCom' -> F NeSysHCom'
nshconsNonTrue' cof i v (F (sys, is)) = case unF cof of
  VCTrue       -> impossible
  VCFalse      -> F (sys, is)
  VCNe cof is' -> F (NSHCons (bindCof cof (bindILazynf i v)) sys // (is <> is'))
{-# inline nshconsNonTrue' #-}

evalSys :: SubArg => NCofArg => DomArg => EnvArg => Sys -> F VSys
evalSys = \case
  SEmpty          -> vsempty
  SCons cof t sys -> vscons (evalCof cof) (evalf t) (evalSys sys)

vshempty :: F VSysHCom
vshempty = F (VSHNe (NSHEmpty, mempty))
{-# inline vshempty #-}

vshcons :: NCofArg => F VCof -> Name -> (NCofArg => F I -> F Val) -> F VSysHCom -> F VSysHCom
vshcons cof i v ~sys = case unF cof of
  VCTrue       -> F (VSHTotal (unF (bindILazy i v)))
  VCFalse     -> sys
  VCNe cof is -> case unF sys of
    VSHTotal v'      -> F $ VSHTotal v'
    VSHNe (sys, is') -> F $ VSHNe (NSHCons (bindCof cof (bindILazynf i v)) sys // is <> is')
{-# inline vshcons #-}

vshconsS :: SubArg => NCofArg => F VCof -> Name -> (SubArg => NCofArg => F I -> F Val)
         -> F VSysHCom -> F VSysHCom
vshconsS cof i v ~sys = case unF cof of
  VCTrue      -> F (VSHTotal (unF (bindILazyS i v)))
  VCFalse     -> sys
  VCNe cof is -> case unF sys of
    VSHTotal v'      -> F $ VSHTotal v'
    VSHNe (sys, is') -> F $ VSHNe (NSHCons (bindCof cof (bindILazySnf i v)) sys //
                                   is <> is')
{-# inline vshconsS #-}

evalSysHCom :: SubArg => NCofArg => DomArg => EnvArg => SysHCom -> F VSysHCom
evalSysHCom = \case
  SHEmpty            -> vshempty
  SHCons cof x t sys -> vshconsS (evalCof cof) x (\_ -> evalf t) (evalSysHCom sys)

occursInNeCof :: NeCof -> IVar -> Bool
occursInNeCof cof i' = case cof of
  NCEq i j    -> i == IVar i' || j == IVar i'
  NCAnd c1 c2 -> occursInNeCof c1 i' || occursInNeCof c2 i'

neCofVars :: NeCof -> IS.IVarSet
neCofVars = \case
  NCEq i j    -> IS.insertI i $ IS.insertI j mempty
  NCAnd c1 c2 -> neCofVars c1 <> neCofVars c2


-- Alternative hcom and com semantics which shortcuts to term instantiation if
-- the system is total. We make use of the knowledge that the system argument
-- comes from the syntax.
----------------------------------------------------------------------------------------------------

data VSysHCom' = VSHTotal' Name Tm | VSHNe' NeSysHCom IS.IVarSet deriving Show

vshempty' :: F VSysHCom'
vshempty' = F $ VSHNe' NSHEmpty mempty

vshconsS' :: SubArg => NCofArg => DomArg => EnvArg => F VCof -> Name -> Tm -> F VSysHCom' -> F VSysHCom'
vshconsS' cof i t ~sys = case unF cof of
  VCTrue      -> F (VSHTotal' i t)
  VCFalse     -> sys
  VCNe cof is -> case unF sys of
    VSHTotal' x t  -> F (VSHTotal' x t)
    VSHNe' sys is' -> F (VSHNe' (NSHCons (bindCof cof (bindILazySnf i \_ -> evalf t)) sys)
                                (is <> is'))
{-# inline vshconsS' #-}

evalSysHCom' :: SubArg => NCofArg => DomArg => EnvArg => SysHCom -> F VSysHCom'
evalSysHCom' = \case
  SHEmpty            -> vshempty'
  SHCons cof x t sys -> vshconsS' (evalCof cof) x t (evalSysHCom' sys)

hcom' :: SubArg => NCofArg => DomArg => EnvArg => F I -> F I -> F Val -> F VSysHCom' -> F Val -> Val
hcom' r r' ~a ~t ~b
  | r == r'                 = unF b
  | VSHTotal' x t  <- unF t = let ?sub = ?sub `ext` unF r' in eval t
  | VSHNe' nsys is <- unF t = hcomdnnf r r' a (F (nsys, is)) b
{-# inline hcom' #-}

com' ::
  SubArg => NCofArg => DomArg => EnvArg => F I -> F I -> F (BindI Val) -> F VSysHCom' -> F Val -> Val
com' r r' ~a ~sys ~b
  | r == r'                   = unF b
  | VSHTotal' x t  <- unF sys = let ?sub = ?sub `ext` unF r' in eval t
  | VSHNe' nsys is <- unF sys = comdnnf r r' a (F (nsys, is)) b
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

mapBindCofLazy :: NCofArg => BindCofLazy a -> (NCofArg => a -> F b) -> F (BindCofLazy b)
mapBindCofLazy t f = bindCofLazy (unBindCofLazy t) (f (t^.body))
{-# inline mapBindCofLazy #-}

mapBindCofLazynf :: NCofArg => BindCofLazy a -> (NCofArg => a -> F b) -> BindCofLazy b
mapBindCofLazynf t f = unF (mapBindCofLazy t f)
{-# inline mapBindCofLazynf #-}

mapBindILazy :: NCofArg => SubAction a => BindILazy a -> (NCofArg => F I -> a -> F b) -> F (BindILazy b)
mapBindILazy t f = bindILazy (t^.name) \i -> f i (t ∙ unF i)
{-# inline mapBindILazy #-}

-- | Map over a binder in a way which *doesn't* rename the bound variable to a
--   fresh one.  In this case, the mapping function cannot refer to values in
--   external scope, it can only depend on the value under the binder. This can
--   be useful when we only do projections under a binder. The case switch in
--   `coed` on the type argument is similar.
unsafeMapBindI :: NCofArg => BindI a -> (NCofArg => a -> F b) -> F (BindI b)
unsafeMapBindI (BindI x i a) f =
  let ?cof = setDomCod (i + 1) i ?cof `ext` IVar i in
  seq ?cof (F (BindI x i (unF (f a))))
{-# inline unsafeMapBindI #-}

unsafeMapBindILazy :: NCofArg => BindILazy a -> (NCofArg => a -> F b) -> F (BindILazy b)
unsafeMapBindILazy (BindILazy x i a) f =
  let ?cof = setDomCod (i + 1) i ?cof `ext` IVar i in
  seq ?cof (F (BindILazy x i (unF (f a))))
{-# inline unsafeMapBindILazy #-}

unsafeMapBindILazynf :: NCofArg => BindILazy a -> (NCofArg => a -> F b) -> BindILazy b
unsafeMapBindILazynf t f = unF (unsafeMapBindILazy t f); {-# inline unsafeMapBindILazynf #-}

mapBindILazynf :: NCofArg => SubAction a => BindILazy a -> (NCofArg => F I -> a -> F b) -> BindILazy b
mapBindILazynf t f = unF (mapBindILazy t f); {-# inline mapBindILazynf #-}

mapNeSys :: NCofArg => (NCofArg => Val -> F Val) -> F NeSys -> F NeSys
mapNeSys f sys = F (go (unF sys)) where
  go :: NeSys -> NeSys
  go = \case
    NSEmpty      -> NSEmpty
    NSCons t sys -> NSCons (mapBindCofLazynf t f) (go sys)
{-# inline mapNeSys #-}

mapNeSysnf :: NCofArg => (NCofArg => Val -> F Val) -> F NeSys -> NeSys
mapNeSysnf f sys = unF (mapNeSys f sys); {-# inline mapNeSysnf #-}

mapNeSys' :: NCofArg => (NCofArg => Val -> F Val)
             -> F (NeSys, IS.IVarSet)
             -> F (NeSys, IS.IVarSet)
mapNeSys' f (F (!sys, !is)) = F (mapNeSysnf f (F sys) // is)
{-# inline mapNeSys' #-}

mapNeSysHCom :: NCofArg => (NCofArg => F I -> Val -> F Val) -> F NeSysHCom -> F NeSysHCom
mapNeSysHCom f sys = F (go (unF sys)) where
  go :: NeSysHCom -> NeSysHCom
  go = \case
    NSHEmpty      -> NSHEmpty
    NSHCons t sys -> NSHCons (mapBindCof t \t -> mapBindILazynf t f) (go sys)
{-# inline mapNeSysHCom #-}

mapNeSysHComnf :: NCofArg => (NCofArg => F I -> Val -> F Val) -> F NeSysHCom -> NeSysHCom
mapNeSysHComnf f sys = unF (mapNeSysHCom f sys); {-# inline mapNeSysHComnf #-}

mapNeSysHCom' :: NCofArg => (NCofArg => F I -> Val -> F Val) -> F NeSysHCom' -> F NeSysHCom'
mapNeSysHCom' f (F (!sys, !is)) = F (mapNeSysHComnf f (F sys) // is)
{-# inline mapNeSysHCom' #-}

mapVSysHCom :: NCofArg => (NCofArg => F I -> Val -> F Val) -> F VSysHCom -> F VSysHCom
mapVSysHCom f sys = case unF sys of
  VSHTotal v      -> F (VSHTotal (mapBindILazynf v f))
  VSHNe (sys, is) -> F (VSHNe (mapNeSysHComnf f (F sys) // is))
{-# inline mapVSysHCom #-}

mapNeSysToH :: NCofArg => (NCofArg => F I -> Val -> F Val) -> F NeSys -> F NeSysHCom
mapNeSysToH f sys = case unF sys of
  NSEmpty      -> F NSHEmpty
  NSCons t sys -> F (NSHCons (bindCof (unBindCofLazy t) (bindILazynf "i" \i -> f i (t^.body)))
                             (unF (mapNeSysToH f (F sys))))
{-# inline mapNeSysToH #-}

mapNeSysToH' :: NCofArg => (NCofArg => F I -> Val -> F Val) -> F NeSys' -> F NeSysHCom'
mapNeSysToH' f (F (!sys, !is)) = F (unF (mapNeSysToH f (F sys)) //is)
{-# inline mapNeSysToH' #-}

mapNeSysFromH :: NCofArg => (NCofArg => BindILazy Val -> F Val) -> F NeSysHCom -> F NeSys
mapNeSysFromH f sys = case unF sys of
  NSHEmpty      -> F NSEmpty
  NSHCons t sys -> F (NSCons (bindCofLazynf (unBindCof t) (f (t^.body)))
                             (unF (mapNeSysFromH f (F sys))))
{-# inline mapNeSysFromH #-}

-- | Map over the (∀i.α) of a system under a binder, returning a NeSysHCom'.
--   The BindI in the function arguments refers to the original component value.
mapForallNeSys' :: NCofArg => (NCofArg => F I -> BindI Val -> F Val) -> BindI NeSys -> F NeSysHCom'
mapForallNeSys' f bind@(BindI x i sys) = case sys of
  NSEmpty -> F (NSHEmpty // mempty)
  NSCons t sys ->
    if occursInNeCof (t^.binds) i
      then mapForallNeSys' f (BindI x i sys)
      else case mapForallNeSys' f (BindI x i sys) of
        F (sys,is) -> F (NSHCons (bindCof (unBindCofLazy t)
                                    (bindILazynf x \j -> f j (rebind (F bind) (t^.body))))
                                 sys
                      // is <> neCofVars (t^.binds))
{-# inline mapForallNeSys' #-}

mapForallNeSysnf' :: NCofArg => (NCofArg => F I -> BindI Val -> F Val) -> BindI NeSys -> NeSysHCom'
mapForallNeSysnf' f sys = unF (mapForallNeSys' f sys)
{-# inline mapForallNeSysnf' #-}


-- System concatenation
----------------------------------------------------------------------------------------------------

catNeSysHCom' :: F (NeSysHCom, IS.IVarSet) -> F (NeSysHCom, IS.IVarSet) -> F (NeSysHCom, IS.IVarSet)
catNeSysHCom' (F (!sys, !is)) (F (!sys', !is')) =
  F $ ((,) $$! catNeSysHCom sys sys' $$! (is <> is'))
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
    VSg (VPi a $ NCl "x" $ CIsEquiv4 a f g) $ NCl "linv" $ CIsEquiv2 a b f g

  CIsEquiv2 a b f g -> let ~linv = u in
    VSg (VPi b $ NCl "x" $ CIsEquiv5 b f g) $ NCl "rinv" $ CIsEquiv3 a b f g linv

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

  CCoeAlong (frc -> a) (frc -> r) (frc -> r') ->
    let ~x = u in coenf r r' a (frc x)

  CCoeLinv0 (frc -> a) (frc -> r) (frc -> r') ->
    let ~x   = frc u
        -- x = g (f x)
        ~lhs = unF x
        ~rhs = coenf r' r a (coe r r' a x)
    in VPLam lhs rhs $ NICl "j" $ ICCoeLinv1 (unF a) (unF r) (unF r') (unF x)

  CCoeRinv0 a r r' ->
    let ~x   = u
        -- f (g x) = x
        ~lhs = let fr = frc r; fr' = frc r'; fa = frc a
               in coenf fr fr' fa (coe fr' fr fa (frc x))
        ~rhs = x
    in VPLam lhs rhs $ NICl "j" $ ICCoeRinv1 a r r' x

  CCoeCoh0 a r r' ->
    let ~x = u

        -- (λ k. coe r r' a x)
        ~lhs = refl (coenf (frc r) (frc r') (frc a) (frc x))

        -- (λ k. rinvfill a r r' (ffill a r r' x) k)
        ~rhs =
           -- coe r r' a (coe r' r a (coe r r' a x))
           let ~fr = frc r; ~fr' = frc r'; ~fa = frc a in

           let ~lhs' = coenf fr fr' fa (coe fr' fr fa (coe fr fr' fa (frc x)))
               ~rhs' = coenf fr fr' fa (frc x) in

           VPLam lhs' rhs' $ NICl "k" $ ICCoeCoh0Rhs a r r' x

    in VPLam lhs rhs $ NICl "l" $ ICCoeCoh1 a r r' x

  CHInd motive ms (frc -> t) ->
    elim motive ms (t ∘ u)


-- | Apply an ivar closure.
icapp :: NCofArg => DomArg => NamedIClosure -> I -> Val
icapp (NICl _ t) arg = case t of
  ICEval s env t ->
    let ?env = env; ?sub = ext s arg in eval t

  -- coe r r' (i. t i ={j. A i j} u i) p =
  --   λ {t r'}{u r'} j. com r r' (i. A i j) [j=0 i. t i; j=1 i. u i] (p {t r} {u r}j)

  ICCoePath (frc -> r) (frc -> r') a lhs rhs p ->
    let j     = frc arg
        abind = bindIf "i" \i -> a ∙ unF i ∘ unF j in
    hcom r r' (a ∙ unF r' ∘ unF j)
      (vshcons (ceq j fi0) "i" (\i -> coe i r' abind (lhs ∘ unF i)) $
       vshcons (ceq j fi1) "i" (\i -> coe i r' abind (rhs ∘ unF i)) $
       vshempty)
      (coe r r' abind (pappf (lhs ∙ unF r) (rhs ∙ unF r) (frc p) j))

    -- com r r' (bindIf "i" \i -> a ∙ unF i ∘ unF j)
    --          (vshcons (ceq j fi0) "i" (\i -> lhs ∘ unF i) $
    --           vshcons (ceq j fi1) "i" (\i -> rhs ∘ unF i) $
    --           vshempty)
    --          (pappf (lhs ∙ unF r) (rhs ∙ unF r) (frc p) j)

  ICHComPath (frc -> r) (frc -> r') a lhs rhs sys p ->
    let farg = frc arg in
    hcom r r' (a ∘ unF farg)
      (vshcons (ceq farg fi0) "i" (\i -> frc lhs) $
       vshcons (ceq farg fi1) "i" (\i -> frc rhs) $
       mapVSysHCom (\_ t -> pappf lhs rhs (frc t) farg)
                   (frc sys))
      (pappf lhs rhs (frc p) farg)

-- hcom r r' (lhs ={j.A j} rhs) [α i. t i] base =
--   λ j. hcom r r' (A j) [j=0 i. lhs; j=1 i. rhs; α i. t i j] (base j)


  ICHComLine (frc -> r) (frc -> r') a sys base ->
    let farg = frc arg in
    hcom r r' (a ∘ unF farg)
      (mapVSysHCom (\_ t -> lappf (frc t) farg) (frc sys))
      (lappf (frc base) farg)

  ICCoeLine (frc -> r) (frc -> r') a p ->
    let j = frc arg in
    coenf r r' (bindIf "i" \i -> a ∙ unF i ∘ unF j) (lappf (frc p) j)

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

  ICCoeLinv1 (frc -> a) (frc -> r) (frc -> r') (frc -> x) ->
    let j = frc arg in linvfill a r r' x j

  ICCoeRinv1 (frc -> a) (frc -> r) (frc -> r') (frc -> x) ->
    let j = frc arg in rinvfill a r r' x j

  ICCoeCoh1 a r r' x ->
    let l    = arg
        ~fa  = frc a
        ~fr  = frc r
        ~fr' = frc r'
        ~fx  = frc x
        ~fl  = frc l

        -- ffill a r r' (linvfill a r r' x l)
        ~lhs = ffillnf fa fr fr' (linvfillf fa fr fr' fx fl)

        -- ffill a r r' x
        ~rhs = ffillnf fa fr fr' fx

    in VPLam lhs rhs $ NICl "k" $ ICCoeCoh2 a r r' x l

  ICCoeCoh2 (frc -> a) (frc -> r) (frc -> r') (frc -> x) (frc -> l) ->
    let k = frc arg in
    coeCoherence a r r' x l k

  -- (λ k. rinvfill a r r' (ffill a r r' x) k)
  ICCoeCoh0Rhs (frc -> a) (frc -> r) (frc -> r') (frc -> x) ->
    let k = frc arg in
    rinvfill a r r' (ffill a r r' x) k

-- | sym (A : U)(x y : A) -> x = y : y = x
--     := λ i*. hcom 0 1 [i=0 j. p j; i=1 j. x] x;
  ICSym a x y p ->
    let i = frc arg in
    hcomd fi0 fi1 (frc a)
          (vshcons (ceq i fi0) "j" (\j -> pappf x y (frc p) j) $
           vshcons (ceq i fi1) "_" (\_ -> frc x) $
           vshempty)
          (frc x)

-- | comp (A : U)(x y z : A) (p : x = y) (q : y = z) : x = z
--    := λ i*. hcom 0 1 A [i=0 j. x; i=1 j. q j] (p i);
  ICTrans a x y z p q ->
    let i = frc arg in
    hcomd fi0 fi1 (frc a)
      (vshcons (ceq i fi0) "_" (\_ -> frc x) $
       vshcons (ceq i fi1) "j" (\j -> pappf y z (frc q) j) $
       vshempty)
      (pappf x y (frc p) i)

-- | ap (A B : U)(f : A -> B)(x y : A)(p : x = y) : f x = f y
--     := λ i*. f (p i)
  ICAp f x y p ->
    let i = frc arg in frc f ∙ papp x y (frc p) i

proj1 :: F Val -> Val
proj1 t = case unF t of
  VPair t _ -> t
  VNe t is  -> VNe (NProj1 t) is
  VTODO     -> VTODO
  _         -> impossible
{-# inline proj1 #-}

proj1f t = frc (proj1 t); {-# inline proj1f  #-}

proj1BindI :: NCofArg => DomArg => BindI Val -> F (BindI Val)
proj1BindI t = unsafeMapBindI t (\t -> proj1f (frc t))
{-# inline proj1BindI #-}

proj2 :: F Val -> Val
proj2 t = case unF t of
  VPair _ u -> u
  VNe t is  -> VNe (NProj2 t) is
  VTODO     -> VTODO
  _         -> impossible
{-# inline proj2 #-}

proj2f t = frc (proj2 t); {-# inline proj2f #-}


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

  -- closed inductives
  VTyCon x ENil ->
    t

  VTyCon x (rebind topA -> ps) ->
    uf

  -- Note: I don't need to rebind the "is"! It can be immediately weakened
  -- to the outer context.
  VNe (rebind topA -> n) is ->
    F (VNe (NCoe (unF r) (unF r') (unF topA) (unF t))
           (IS.insertI (unF r) $ IS.insertI (unF r') is))

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

    gr       = t
    ~_Ar'    = a ∘ unF r'
    ~topSysr = topSys ∘ unF r
    ~frc_a   = frc a

  -- ar' : Ar'
  -- ar' := comp r r' (i. A i) [(∀i.α) i. f i (coe r i (j. T j) gr)] (unglue gr sysr)

    ~ar' = hcomdn r r' _Ar'
             (mapForallNeSys'
                (\i tf -> coe i r' frc_a (proj1f (proj2f (tf ∘ unF i)) ∘ coenf r i (proj1BindI tf) gr))
                topSys)
             (coed r r' frc_a (ungluef (unF gr) topSysr))

    -- ~ar' = comdn r r' (frc a)
    --          (mapForallNeSys'
    --             (\i tf -> proj1f (proj2f (tf ∘ unF i)) ∘ coenf r i (proj1BindI tf) gr)
    --             topSys)
    --          (ungluef (unF gr) topSysr)

    mkComponents :: NCofArg => Val -> (F Val, BindILazy Val)
    mkComponents tfr' = seq ?cof $ let
      ~equiv1  = frc tfr'
      ~equiv2  = proj2f equiv1
      ~equiv3  = proj2f equiv2
      ~equiv4  = proj2f equiv3
      ~equiv5  = proj2f equiv4
      ~tr'     = proj1f equiv1
      ~fr'     = proj1f equiv2
      ~fr'inv  = proj1f equiv3
      ~r'linv  = proj1f equiv4
      ~r'rinv  = proj1f equiv5
      ~r'coh   = proj2f equiv5
      ~fibval  = fr'inv ∘ unF ar'
      ~fibpath = r'rinv ∘ unF ar'

      -- shorthands for path applications
      app_r'linv ~x i =
        pappf x (fr'inv ∙ (fr' ∙ x)) (r'linv ∘ x) i

      app_r'coh ~x i j =
        pappf (fr' ∙ unF (app_r'linv x i))
              (fr' ∙ x)
              (pappf (refl (fr' ∙ x)) (r'rinv ∙ (fr' ∙ x)) (r'coh ∘ x) i)
              j

      -- valSys = [r=r'  i. fr'.linv gr i
      --         ;(∀i.α) i. fr'.linv (coe r r' (i. T i) gr) i]
      ~valSys = nshconsNonTrue' (ceq r r') "i" (\i -> app_r'linv (unF gr) i) $
                mapForallNeSys' (\i tf -> app_r'linv (coenf r r' (proj1BindI tf) gr) i) topSys

      -- fibval* : Tr'
      -- fibval* = hcom 1 0 Tr' valSys fibval
      ~fibval' = hcomdn fi1 fi0 tr' valSys fibval

      -- fibpath* : fr' fibval = ar'
      -- fibpath* = λ j.
      --    hcom 1 0 (A r') [j=0    i. fr' (hcom 1 i Tr' valSys fibval)    -- no need to force valSys because
      --                    ;j=1    i. ar'                                 -- it's independent from j=0
      --                    ;r=r'   i. fr'.coh gr i
      --                    ;(∀i.α) i. fr'.coh (coe r r' (i. T i) gr) i]
      --                    (fibpath {fr' fibval} {ar'} j)
      fibpath' = bindILazynf "i" \j ->
        hcomdf fi1 fi0 _Ar'
          (vshcons (ceq j fi0) "i" (\i -> fr' ∘ hcomnnf fi1 i tr' valSys fibval) $
           vshcons (ceq j fi1) "i" (\i -> ar') $
           F $ VSHNe $ unF $
           nshconsNonTrue' (ceq r r') "i" (\i -> app_r'coh (unF gr) i j) $
           mapForallNeSys' (\i tf -> app_r'coh (coenf r r' (proj1BindI tf) gr) i j) topSys
          )
          (pappf (fr' ∙ unF fibval) (unF ar') fibpath j)

      in (fibval', fibpath')

    mkNeSystems :: NeSys -> (NeSys, NeSysHCom)
    mkNeSystems = \case
      NSEmpty         -> NSEmpty // NSHEmpty
      NSCons tfr' sys -> let
        alphar' = tfr'^.binds
        (fibval  , !fibpath)  = assumeCof alphar' $ mkComponents (tfr'^.body)
        (!fibvals, !fibpaths) = mkNeSystems sys
        in NSCons (BindCofLazy alphar' (unF fibval)) fibvals // NSHCons (BindCof alphar' fibpath) fibpaths

    (!fibvals, !fibpaths) = case unF (topSys ∘ unF r') of
      VSTotal tfr'   -> let
        (!fibval, !fibpath) = mkComponents (unF tfr')
        in F (VSTotal fibval) // F (VSHTotal fibpath)
      VSNe (sys, is) -> let
        (!fibvals, !fibpaths) = mkNeSystems sys
        in F (VSNe (fibvals, is)) // F (VSHNe (fibpaths, is))

    in glue
         (hcomd fi1 fi0 _Ar' (vshcons (ceq r r') "i" (\i -> ungluef (unF gr) topSysr) fibpaths) ar')
         fibvals

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
  | r == r'               = unF b
  | VSHTotal v <- unF sys = v ∙ unF r'
  | VSHNe sys  <- unF sys = comdnnf r r' a (F sys) b
{-# inline com #-}


-- | HCom with off-diagonal I args ("d") and neutral system arg ("n").
hcomdn :: F I -> F I -> F Val -> F (NeSysHCom, IS.IVarSet) -> F Val -> NCofArg => DomArg => F Val
hcomdn r r' a ts@(F (!nts, !is)) base = case unF a of

  VPi a b ->
    F $ VLam $ NCl (b^.name) $ CHComPi (unF r) (unF r') a b nts (unF base)

  VSg a b ->
    let bbind =
         bindIf "i" \i ->
          b ∘ hcomnnf r i
               (frc a)
               (mapNeSysHCom' (\_ t -> proj1f (frc t)) ts)
               (proj1f base) in
    F $ VPair
      (hcomdnnf r r'
        (frc a)
        (mapNeSysHCom' (\_ t -> proj1f (frc t)) ts)
        (proj1f base))
      (hcomdnnf r r'
        (b ∘ hcomnnf r r'
             (frc a)
             (mapNeSysHCom' (\_ t -> proj1f (frc t)) ts)
             (proj1f base))
        (mapNeSysHCom' (\i t -> coe i r' bbind (proj2f (frc t))) ts)
        (coed r r' bbind (proj2f base)))

  -- VSg a b ->
  --   F $ VPair
  --     (hcomdnnf r r'
  --       (frc a)
  --       (mapNeSysHCom' (\_ t -> proj1f (frc t)) ts)
  --       (proj1f base))
  --     (comdnnf r r'
  --       (bindIf "i" \i ->
  --         b ∘ hcomnnf r i
  --              (frc a)
  --              (mapNeSysHCom' (\_ t -> proj1f (frc t)) ts)
  --              (proj1f base))
  --       (mapNeSysHCom' (\_ t -> proj2f (frc t)) ts)
  --       (proj2f base))

  -- (  hcom r r' A [α i. (t i).1] b.1
  --  , com r r' (i. B (hcom r i A [α j. (t j).1] b.1)) [α i. (t i).2] b.2)



  VPath a lhs rhs ->
    F $ VPLam lhs rhs
      $ NICl (a^.name)
      $ ICHComPath (unF r) (unF r') a lhs rhs nts (unF base)

  a@(VNe n is') ->
    F $ VNe (NHCom (unF r) (unF r') a nts (unF base))
            (IS.insertFI r $ IS.insertFI r' $ is <> is')

  -- hcom r r' U [α i. t i] b =
  --   Glue b [r=r'. (b, idEquiv); α. (t r', (coe r' r (i. t i), coeIsEquiv))]

  VU -> let

    -- NOTE the nsconsNonTrue; ceq r r' can be false or neutral
    sys = nsconsNonTrue (ceq r r') (F $ VPair (unF base) (theIdEquiv (unF base))) $
          mapNeSysFromH
            (\t -> F $ VPair (t ∙ unF r')
                     $ theCoeEquiv (bindI (t^.name) \i -> t ∙ unF i)
                                   (unF r') (unF r))
            (F nts)

    in F $ VGlueTy (unF base) (unF sys // (IS.insertI (unF r) $ IS.insertI (unF r') is))

-- hcom for Glue
--------------------------------------------------------------------------------

  -- hcom r r' (Glue [α. (T, f)] A) [β i. t i] gr =
  --   glue (hcom r r' A [β i. unglue (t i); α i. f (hcom r i T [β. t] gr)] (unglue gr))
  --        [α. hcom r r' T [β i. t i] gr]

  VGlueTy a (alphasys, alphais) ->
    let gr        = base
        alphasys' = F (alphasys, alphais)
        betasys   = nts
        betais    = is
        betasys'  = F (betasys, betais)

        -- [α. hcom r r' T [β i. t i] gr]
        fib = mapNeSys
                (\t -> hcomdn r r' (proj1f (frc t)) betasys' gr)
                (F alphasys)

        -- hcom r r' A [  β i. unglue (t i)
        --              ; α i. f (hcom r i T [β. t] gr)]
        --             (unglue gr)
        base =
          hcomdn r r' (frc a)
            (catNeSysHCom'
               (mapNeSysHCom'
                  (\_ t -> ungluenf t alphasys')
                  betasys')
               (mapNeSysToH'
                  (\i (frc -> tf) ->
                      let ty  = proj1f tf              -- T
                          f   = proj1f (proj2f tf) in  -- f
                      f ∘ hcomnnf r i ty betasys' gr
                    )
                  alphasys')
              )
            (ungluenf (unF gr) alphasys')

    in F $ VNe (NGlue (unF base) (unF fib))
               (IS.insertI (unF r) $ IS.insertI (unF r') (alphais <> betais))

  VLine a ->
    F $ VLLam
      $ NICl (a^.name)
      $ ICHComLine (unF r) (unF r') a nts (unF base)

  a@(VTyCon x ps) -> case unF base of
    VDCon x i sp     -> case ?dom of
                          0 -> hcomind0 r r' (F a) ts ps x i sp
                          _ -> hcomind  r r' (F a) ts ps x i sp
    base@(VNe n is') -> F $ VNe (NHCom (unF r) (unF r') a nts base)
                                (IS.insertFI r $ IS.insertFI r' $ is <> is')
    VTODO            -> F VTODO
    _                -> impossible

  a ->
    error $ show a


----------------------------------------------------------------------------------------------------

-- | HCom with nothing known about semantic arguments.
hcom :: NCofArg => DomArg => F I -> F I -> F Val -> F VSysHCom -> F Val -> Val
hcom r r' ~a ~t ~b
  | r == r'             = unF b
  | VSHTotal v <- unF t = v ∙ unF r'
  | VSHNe sys  <- unF t = hcomdnnf r r' a (F sys) b
{-# inline hcom #-}

-- | HCom with neutral system input.
hcomn :: NCofArg => DomArg => F I -> F I -> F Val -> F (NeSysHCom, IS.IVarSet) -> F Val -> F Val
hcomn r r' ~a ~sys ~b
  | r == r' = b
  | True    = hcomdn r r' a sys b
{-# inline hcomn #-}

-- | Off-diagonal HCom.
hcomd :: NCofArg => DomArg => F I -> F I -> F Val -> F VSysHCom -> F Val -> Val
hcomd r r' ~a ~sys ~b
  | VSHTotal v <- unF sys = v ∙ unF r'
  | VSHNe sys  <- unF sys = hcomdnnf r r' a (F sys) b
{-# inline hcomd #-}

hcomnnf r r' ~a ~sys ~b = unF (hcomn r r' a sys b); {-# inline hcomnnf #-}
hcomdnnf r r' a sys base = unF (hcomdn r r' a sys base); {-# inline hcomdnnf #-}
hcomf r r' ~a ~t ~b = frc (hcom r r' a t b); {-# inline hcomf  #-}
hcomdf r r' ~a ~sys ~b = frc (hcomd r r' a sys b); {-# inline hcomdf #-}

glueTy :: NCofArg => DomArg => Val -> F VSys -> Val
glueTy ~a sys = case unF sys of
  VSTotal b -> proj1 b
  VSNe sys  -> VGlueTy a sys
{-# inline glueTy #-}

glueTyf ~a sys = frc (glueTy a sys); {-# inline glueTyf #-}

gluen :: Val -> F NeSys' -> Val
gluen ~t (F (!sys, !is)) = VNe (NGlue t sys) is
{-# inline gluen #-}

glue :: Val -> F VSys -> F Val
glue ~t sys = case unF sys of
  VSTotal v      -> v
  VSNe (sys, is) -> F (VNe (NGlue t sys) is)
{-# inline glue #-}

gluenf ~t sys = unF (glue t sys); {-# inline gluenf #-}

unglue :: NCofArg => DomArg => Val -> F VSys -> Val
unglue ~t sys = case unF sys of
  VSTotal teqv   -> proj1f (proj2f teqv) ∙ t
  VSNe (sys, is) -> VNe (NUnglue t sys) is
{-# inline unglue #-}

ungluen :: NCofArg => DomArg => Val -> F (NeSys, IS.IVarSet) -> Val
ungluen ~t (F (!sys, !is)) = VNe (NUnglue t sys) is
{-# inline ungluen #-}

ungluef  ~t sys = frc (unglue t sys); {-# inline ungluef #-}
ungluenf ~t sys = F (ungluen t sys); {-# inline ungluenf #-}


-- Strict inductive types
----------------------------------------------------------------------------------------------------
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

elim :: NCofArg => DomArg => Val -> VMethods -> F Val -> Val
elim ~motive ms val = case unF val of
  VDCon _ i sp -> lookupMethod i motive ms sp
  VNe n is     -> VNe (NElim motive ms n) is
  VTODO        -> VTODO
  _            -> impossible
{-# inline elim #-}

elimf ~motive ms val = frc (elim motive ms val); {-# inline elimf #-}

projsp :: NCofArg => DomArg => Lvl -> VDSpine -> F Val
projsp ix sp = case (ix, sp) of
  (0 , VDInd t _     ) -> frc t
  (0 , VDHInd t _ _  ) -> frc t
  (0 , VDExt t _ _   ) -> frc t
  (ix, VDInd _ sp    ) -> projsp (ix - 1) sp
  (ix, VDHInd _ _ sp ) -> projsp (ix - 1) sp
  (ix, VDExt _ _ sp  ) -> projsp (ix - 1) sp
  _                    -> impossible

lazyprojfield :: NCofArg => DomArg => Lvl -> Lvl -> Val -> F Val
lazyprojfield conix fieldix v = case unF (frc v) of
  VDCon x i sp | i == conix -> projsp fieldix sp
  _                         -> impossible
{-# inline lazyprojfield #-}

-- Project all fieldix fields of a constructor conix from a system
lazyprojsys :: NCofArg => DomArg => Lvl -> Lvl -> NeSysHCom -> NeSysHCom
lazyprojsys conix fieldix = \case
  NSHEmpty      -> NSHEmpty
  NSHCons t sys -> NSHCons (mapBindCof t \t -> unsafeMapBindILazynf t (lazyprojfield conix fieldix))
                           (lazyprojsys conix fieldix sys)

lazyprojsys' :: NCofArg => DomArg => Lvl -> Lvl -> F NeSysHCom' -> F NeSysHCom'
lazyprojsys' conix fieldix (F (!sys, !is)) = F (lazyprojsys conix fieldix sys // is)
{-# inline lazyprojsys' #-}

hcomind0sp :: NCofArg => DomArg =>
              F I -> F I -> F Val -> F NeSysHCom' -> Env -> Lvl -> Lvl -> VDSpine -> VDSpine
hcomind0sp r r' topa sys ext conix fieldix sp = case sp of
  VDNil ->
    VDNil
  VDInd t sp ->
    VDInd (hcomdnnf r r' topa (lazyprojsys' conix fieldix sys) (frc t))
          (hcomind0sp r r' topa sys ext conix (fieldix + 1) sp)
  VDHInd t a sp ->
    let ft = frc t in
    let va = (let ?env = ext; ?sub = idSub (dom ?cof) in eval a) in
    VDHInd (hcomdnnf r r' (funf va (unF topa)) (lazyprojsys' conix fieldix sys) ft)
           a
           (hcomind0sp r r' topa sys (EDef ext (unF ft)) conix (fieldix + 1) sp)
  VDExt t a sp  ->
    let ft = frc t in
    let ~va = (let ?env = ext; ?sub = idSub (dom ?cof) in evalf a) in
    VDExt (hcomdnnf r r' va (lazyprojsys' conix fieldix sys) ft)
          a
          (hcomind0sp r r' topa sys (EDef ext (unF ft)) conix (fieldix + 1) sp)

hcomind0 :: NCofArg => DomArg =>
            F I -> F I -> F Val -> F NeSysHCom' -> Env -> Lvl -> Lvl -> VDSpine -> F Val
hcomind0 r r' a sys ext tyix conix sp =
  F $ VDCon tyix conix (hcomind0sp r r' a sys ext conix 0 sp)
{-# inline hcomind0 #-}


-- System where all components are known to be the same constructor
data Projected
  = PNil
  | PCons NeCof Name IVar VDSpine Projected

type Projected' = (Projected, IS.IVarSet)

-- TODO: unbox
data TryToProject
  = TTPProject Projected
  | TTPNe {-# unpack #-} NeSysHCom'

projsys :: NCofArg => DomArg => Lvl -> NeSysHCom' -> NeSysHCom -> TryToProject
projsys conix topSys@(!_,!_) = \case
  NSHEmpty      -> TTPProject PNil
  NSHCons t sys ->
    let ~prj = projsys conix topSys sys; {-# inline prj #-} in

    assumeCof (t^.binds) $ case unF(frc (t^.body))^.body of
      VDCon _ conix' sp | conix == conix' ->
        case prj of
          TTPProject prj ->
            TTPProject (PCons (t^.binds) (t^.body.name) (t^.body.binds) sp prj)
          prj@TTPNe{} ->
            prj

      VNe n is -> TTPNe (fst topSys // is <> snd topSys) -- extend blockers with is'
      _        -> impossible

projsys' :: NCofArg => DomArg => Lvl -> F NeSysHCom' -> TryToProject
projsys' conix (F (!sys, !is)) = projsys conix (sys,is) sys
{-# inline projsys' #-}

projfields :: Projected -> Lvl -> NeSysHCom
projfields prj fieldix = case prj of
  PNil ->
    NSHEmpty
  PCons ncof x i sp prj ->
    NSHCons (BindCof ncof (BindILazy x i uf)) (projfields prj fieldix)

projfields' :: Projected' -> Lvl -> F NeSysHCom'
projfields' (!prj,!is) fieldix = F (projfields prj fieldix // is)
{-# inline projfields' #-}

hcomindsp :: NCofArg => DomArg =>
              F I -> F I -> F Val -> Projected' -> Env -> Lvl -> Lvl -> VDSpine -> VDSpine
hcomindsp r r' topa prj@(!_,!_) ext conix fieldix sp = case sp of
  VDNil ->
    VDNil
  VDInd t sp ->
    VDInd (hcomdnnf r r' topa (projfields' prj fieldix) (frc t))
          (hcomindsp r r' topa prj ext conix (fieldix + 1) sp)
  VDHInd t a sp ->
    let ft = frc t in
    let va = (let ?env = ext; ?sub = idSub (dom ?cof) in eval a) in
    VDHInd (hcomdnnf r r' (funf va (unF topa)) (projfields' prj fieldix) ft)
           a
           (hcomindsp r r' topa prj (EDef ext (unF ft)) conix (fieldix + 1) sp)

  VDExt t a sp  ->
    let ft = frc t in
    let ~va = (let ?env = ext; ?sub = idSub (dom ?cof) in evalf a) in
    VDExt (hcomdnnf r r' va (projfields' prj fieldix) ft)
          a
          (hcomindsp r r' topa prj (EDef ext (unF ft)) conix (fieldix + 1) sp)

hcomind :: NCofArg => DomArg =>
           F I -> F I -> F Val -> F NeSysHCom' -> Env -> Lvl -> Lvl -> VDSpine -> F Val
hcomind r r' a sys ext tyix conix sp = case projsys' conix sys of
  TTPProject prj ->
    F $ VDCon tyix conix (hcomindsp r r' a (prj // snd (unF sys)) ext conix 0 sp)
  TTPNe (sys,is) ->
    F $ VNe (NHCom (unF r) (unF r') (unF a) sys (VDCon tyix conix sp))
            (IS.insertI (unF r) $ IS.insertI (unF r') is)
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
  App t u           -> evalf t ∙ eval u
  Lam x t           -> VLam (NCl x (CEval (EC ?sub ?env t)))

  -- Sigma
  Sg x a b          -> VSg (eval a) (NCl x (CEval (EC ?sub ?env b)))
  Pair t u          -> VPair (eval t) (eval u)
  Proj1 t           -> proj1 (evalf t)
  Proj2 t           -> proj2 (evalf t)

  -- U
  U                 -> VU

  -- Path
  Path x a t u      -> VPath (NICl x (ICEval ?sub ?env a)) (eval t) (eval u)
  PApp l r t i      -> papp (eval l) (eval r) (evalf t) (evalI i)
  PLam l r x t      -> VPLam (eval l) (eval r) (NICl x (ICEval ?sub ?env t))

  -- Kan
  Coe r r' x a t    -> coenf (evalI r) (evalI r') (bindIS x \_ -> evalf a) (evalf t)
  HCom r r' a t b   -> hcom' (evalI r) (evalI r') (evalf a) (evalSysHCom' t) (evalf b)

  -- Glue
  GlueTy a sys      -> glueTy (eval a) (evalSys sys)
  Glue t sys        -> gluenf (eval t) (evalSys sys)
  Unglue t sys      -> unglue (eval t) (evalSys sys)

  -- Line
  Line x a          -> VLine (NICl x (ICEval ?sub ?env a))
  LApp t i          -> lapp (evalf t) (evalI i)
  LLam x t          -> VLLam (NICl x (ICEval ?sub ?env t))

  -- Misc
  WkI _ t           -> wkIS (eval t)
  TODO              -> VTODO

  -- Builtins
  Refl t            -> refl (eval t)
  Sym a x y p       -> sym (eval a) (eval x) (eval y) (eval p)
  Trans a x y z p q -> trans (eval a) (eval x) (eval y) (eval z) (eval p) (eval q)
  Ap f x y p        -> ap_ (eval f) (eval x) (eval y) (eval p)
  Com r r' i a t b  -> com' (evalI r) (evalI r') (bindIS i \_ -> evalf a) (evalSysHCom' t) (evalf b)

  -- Inductives
  TyCon x ts        -> VTyCon x (tyParams ts)
  DCon x i sp       -> VDCon x i (dSpine sp)
  Elim mot met t    -> elim (eval mot) (methods met) (evalf t)


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
    NCAnd c1 c2 -> case unF (frc c1) of
      VCTrue -> frc c2
      VCFalse -> cfalse
      VCNe cof is -> let ?cof = cof^.extended in case unF (frc c2) of
        VCTrue        -> F $ VCNe cof is
        VCFalse       -> cfalse
        VCNe cof' is' -> F $ VCNe (NeCof' (cof'^.extended) (NCAnd (cof^.extra) (cof'^.extra)))
                                  (is <> is')

  frcS = \case
    NCEq i j    -> ceq (frcS i) (frcS j)
    NCAnd c1 c2 -> case unF (frcS c1) of
      VCTrue -> frcS c2
      VCFalse -> cfalse
      VCNe cof is -> let ?cof = cof^.extended in case unF (frcS c2) of
        VCTrue        -> F $ VCNe cof is
        VCFalse       -> cfalse
        VCNe cof' is' -> F $ VCNe (NeCof' (cof'^.extended) (NCAnd (cof^.extra) (cof'^.extra)))
                                  (is <> is')

instance Force Val Val where
  frc = \case
    VSub v s                             -> let ?sub = s in frcS v
    VNe t is            | isUnblocked is -> frc t
    VGlueTy a (sys, is) | isUnblocked is -> glueTyf a (frc sys)
    v                                    -> F v

  frcS = \case
    VSub v s                              -> let ?sub = sub s in frcS v
    VNe t is            | isUnblockedS is -> frcS t
    VGlueTy a (sys, is) | isUnblockedS is -> glueTyf (sub a) (frcS sys)

    VNe t is      -> F (VNe (sub t) (sub is))
    VGlueTy a sys -> F (VGlueTy (sub a) (sub sys))
    VPi a b       -> F (VPi (sub a) (sub b))
    VLam t        -> F (VLam (sub t))
    VPath a t u   -> F (VPath (sub a) (sub t) (sub u))
    VPLam l r t   -> F (VPLam (sub l) (sub r) (sub t))
    VSg a b       -> F (VSg (sub a) (sub b))
    VPair t u     -> F (VPair (sub t) (sub u))
    VU            -> F VU
    VTODO         -> F VTODO
    VLine t       -> F (VLine (sub t))
    VLLam t       -> F (VLLam (sub t))
    VTyCon x ts   -> F (VTyCon x (sub ts))
    VDCon x i sp  -> F (VDCon x i (sub sp))

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
    NGlue t sys       -> glue t (frc sys)
    NLApp t i         -> lappf (frc t) (frc i)
    NElim mot ms t    -> elimf mot ms (frc t)

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
    NGlue t sys       -> glue (sub t) (frcS sys)
    NLApp t i         -> lappf (frcS t) (frcS i)
    NElim mot ms t    -> elimf (sub mot) (sub ms) (frcS t)

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
        VSHTotal v'      -> F (VSHTotal v')
        VSHNe (sys, is') -> F (VSHNe (NSHCons (bindCof cof (unF (frc (t^.body)))) sys // is <> is'))

  frcS = \case
    NSHEmpty ->
      vshempty
    NSHCons t sys -> case unF (frcS (t^.binds)) of
      VCTrue      -> F (VSHTotal (unF (frcS (t^.body))))
      VCFalse     -> frcS sys
      VCNe cof is -> case unF (frcS sys) of
        VSHTotal v'      -> F (VSHTotal v')
        VSHNe (sys, is') -> F (VSHNe (NSHCons (bindCof cof (unF (frcS (t^.body)))) sys // is <> is'))

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
  NSub n s           -> let ?sub = sub s in unSubNeS n
  NLocalVar x        -> NLocalVar x
  NApp t u           -> NApp (sub t) (sub u)
  NPApp l r p i      -> NPApp (sub l) (sub r) (sub p) (sub i)
  NProj1 t           -> NProj1 (sub t)
  NProj2 t           -> NProj2 (sub t)
  NCoe r r' a t      -> NCoe (sub r) (sub r') (sub a) (sub t)
  NHCom r r' a sys t -> NHCom (sub r) (sub r') (sub a) (sub sys) (sub t)
  NUnglue a sys      -> NUnglue (sub a) (sub sys)
  NGlue a sys        -> NGlue (sub a) (sub sys)
  NLApp t i          -> NLApp (sub t) (sub i)
  NElim mot ms t     -> NElim (sub mot) (sub ms) (sub t)

----------------------------------------------------------------------------------------------------
-- Definitions
----------------------------------------------------------------------------------------------------

fun :: Val -> Val -> Val
fun a b = VPi a $ NCl "_" $ CConst b

funf :: Val -> Val -> F Val
funf a b = F $ VPi a $ NCl "_" $ CConst b

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
                VPLam (ff ∙ x) (ff ∙ y) $ NICl "i" $ ICAp (unF ff) x y p

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

ffill :: NCofArg => DomArg => F (BindI Val) -> F I -> F I -> F Val -> F Val
ffill a r i x = coe r i a x; {-# inline ffill #-}

ffillnf a r i x = unF (ffill a r i x); {-# inline ffillnf #-}

gfill :: NCofArg => DomArg => F (BindI Val) -> F I -> F I -> F Val -> F Val
gfill a r i x = coe i r a x; {-# inline gfill #-}

linvfill :: NCofArg => DomArg => F (BindI Val) -> F I -> F I -> F Val -> F I -> Val
linvfill a r i x j =
  hcom r i (unF a ∘ unF r)
    (vshcons (ceq j fi0) "k" (\_ -> x) $
     vshcons (ceq j fi1) "k" (\k -> coe k r a (coe r k a x)) $
     vshempty)
    x

linvfillf a r i x j = frc (linvfill a r i x j); {-# inline linvfillf #-}

rinvfill :: NCofArg => DomArg => F (BindI Val) -> F I -> F I -> F Val -> F I -> Val
rinvfill a r i x j =
  hcom i r (unF a ∘ unF i)
    (vshcons (ceq j fi0) "k" (\k -> coe k i a (coe i k a x)) $
     vshcons (ceq j fi1) "k" (\k -> x) $
     vshempty)
    x

rinvfillf a r i x j = frc (rinvfill a r i x j); {-# inline rinvfillf #-}

coeCoherence :: NCofArg => DomArg => F (BindI Val) -> F I -> F I -> F Val -> F I -> F I -> Val
coeCoherence a r r' x l k =
  hcom r r' (unF a ∘ unF r')
    (vshcons (ceq k fi0) "i" (\i -> coe i r' a (ffill a r i (linvfillf a r i x l))) $
     vshcons (ceq k fi1) "i" (\i -> coe i r' a (ffill a r i x)) $
     vshcons (ceq l fi0) "i" (\i -> coe i r' a (ffill a r i x)) $
     vshcons (ceq l fi1) "i" (\i -> coe i r' a (rinvfillf a r i (ffill a r i x) k)) $
     vshempty)
    (coe r r' a x)

  -- -- with com
  -- com r r' a
  --   (vshcons (ceq k fi0) "i" (\i -> ffill a r i (linvfillf a r i x l)) $
  --    vshcons (ceq k fi1) "i" (\i -> ffill a r i x) $
  --    vshcons (ceq l fi0) "i" (\i -> ffill a r i x) $
  --    vshcons (ceq l fi1) "i" (\i -> rinvfillf a r i (ffill a r i x) k) $
  --    vshempty)
  --   x

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
