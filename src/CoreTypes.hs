{-# options_ghc -funbox-strict-fields #-}

module CoreTypes where

import qualified IVarSet as IS
import Common
import Interval
import Substitution

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

  | PathP Name Ty Tm Tm       -- PathP i.A x y
  | PApp ~Tm ~Tm Tm I         -- (x : A i0)(y : A i1)(t : PathP i.A x y)(j : I)
  | PLam ~Tm ~Tm Name Tm      -- endpoints, body

  | Coe I I Name Ty Tm        -- coe r r' i.A t
  | HCom I I Name ~Ty Sys Tm  -- hcom r r' i A [α → t] u

  -- we switch the field orders here compared to the papers, because
  -- this one is the sensible "dependency" order
  | GlueTy Ty Sys            -- Glue A [α ↦ B]      (B : Σ X (X ≃ A))
  | Glue   Tm ~Sys           -- glue a [α ↦ b]
  | Unglue Tm ~Sys           -- unglue g [α ↦ B]

  | Nat
  | Zero
  | Suc Tm
  | NatElim Tm Tm Tm Tm      -- (P : Nat -> U) -> P z -> ((n:_) -> P n -> P (suc n)) -> (n:_) -> P n
  deriving Show

-- | Atomic equation.
data CofEq = CofEq I I
  deriving Show

-- | Conjunction of equations.
data Cof = CTrue | CAnd CofEq Cof
  deriving Show

data Sys = SEmpty | SCons Cof Tm Sys
  deriving Show


-- Values
--------------------------------------------------------------------------------

data NamedClosure = NCl {
    namedClosureName    :: Name
  , namedClosureClosure :: Closure }
  deriving Show

data NamedIClosure = NICl {
    namedIClosureName    :: Name
  , namedIClosureClosure :: IClosure }
  deriving Show

data NeCof
  = NCEq I I
  | NCAnd NeCof NeCof
  deriving Show

data VCof
  = VCTrue
  | VCFalse
  | VCNe NeCof IS.IVarSet
  deriving Show

data Env
  = ENil
  | EDef Env ~Val
  deriving Show

type EnvArg = (?env :: Env)

data BindI a = BindI {
    bindIName  :: Name
  , bindIBinds :: IVar
  , bindIBody  :: a}
  deriving Show

data BindILazy a = BindILazy {
    bindILazyName  :: Name
  , bindILazyBinds :: IVar
  , bindILazyBody  :: ~a}
  deriving Show

data BindCof a = BindCof {
    bindCofBinds :: NeCof
  , bindCofBody  :: a}
  deriving Show

data BindCofLazy a = BindCofLazy {
    bindCofLazyBinds :: NeCof
  , bindCofLazyBody  :: ~a}
  deriving Show

data NeSys
  = NSEmpty
  | NSCons (BindCofLazy Val) NeSys
  deriving Show

data NeSysSub
  = NSSNe NeSys
  | NSSSub NeSys Sub
  deriving Show

data NeSysHCom
  = NSHEmpty
  | NSHCons (BindCof (BindILazy Val)) NeSysHCom
  deriving Show

data NeSysHComSub
  = NSHSNe NeSysHCom
  | NSHSSub NeSysHCom Sub
  deriving Show

-- TODO: unbox
data VSys
  = VSTotal ~Val
  | VSNe NeSys IS.IVarSet
  deriving Show

-- TODO: unbox
data VSysHCom
  = VSHTotal (BindILazy Val)
  | VSHNe NeSysHCom IS.IVarSet
  deriving Show

type VTy = Val

data Val
  = VSub Val Sub

  -- Neutrals. These are annotated with sets of blocking ivars. Glue types are
  -- also neutral, but they're handled separately, because we have to match on
  -- them in coe/hcom.
  | VNe Ne IS.IVarSet
  | VGlueTy VTy NeSysSub IS.IVarSet

  -- canonicals
  | VPi VTy NamedClosure
  | VLam NamedClosure
  | VPathP NamedIClosure Val Val
  | VPLam ~Val ~Val NamedIClosure  -- annotated with endpoints
  | VSg VTy NamedClosure
  | VPair Val Val
  | VU

  | VNat
  | VZero
  | VSuc Val
  deriving Show

data Ne
  = NLocalVar Lvl
  | NSub Ne Sub
  | NApp Ne Val
  | NPApp Ne ~Val ~Val I
  | NProj1 Ne
  | NProj2 Ne
  | NCoe I I (BindI Val) Val
  | NHCom I I VTy NeSysHComSub Val
  | NUnglue Val NeSysSub
  | NGlue Val NeSysSub
  | NNatElim Val Val Val Ne
  deriving Show

--------------------------------------------------------------------------------

vVar :: Lvl -> Val
vVar x = VNe (NLocalVar x) mempty
{-# inline vVar #-}

newtype F a = F {unF :: a}
  deriving (SubAction, Show) via a

type DomArg = (?dom :: Lvl)    -- fresh LocalVar

--------------------------------------------------------------------------------

-- | Defunctionalized closures.
data Closure
  -- ^ Body of vanilla term evaluation.
  = CEval Sub Env Tm

  -- ^ Body of function coercions.
  | CCoePi I I (BindI VTy) (BindI NamedClosure) Val

  -- ^ Body of function hcom.
  | CHComPi I I VTy NamedClosure NeSysHComSub Val

--   | CConst Val

--   | C'λ'a''a        -- λ a. a
--   | C'λ'a'i''a      -- λ a i. a
--   | C'λ'a'i'j''a    -- λ a i j. a

--   | CCoeInv Val I I
--   | CCoeLinv0 Val I I
--   | CCoeRinv0 Val I I


-- -- isEquiv : (A → B) → U
-- -- isEquiv A B f :=
-- --     (g^1    : B → A)
-- --   × (linv^2 : (x^4 : A) → Path A x (g (f x)))
-- --   × (rinv^3 : (x^5 : B) → Path B (f (g x)) x)
-- --   × (coh    : (x^6 : A) →
-- --             PathP (i^7) (Path B (f (linv x {x}{g (f x)} i)) (f x))
-- --                   (refl B (f x))
-- --                   (rinv (f x)))

--   | CIsEquiv1 Val Val Val         -- A B f
--   | CIsEquiv2 Val Val Val Val     -- A B f g
--   | CIsEquiv3 Val Val Val Val Val -- A B f g linv
--   | CIsEquiv4 Val Val Val         -- A f g
--   | CIsEquiv5 Val Val Val         -- B f g
--   | CIsEquiv6 Val Val Val Val Val -- B f g linv rinv


--   -- [A, B]  equiv A B = (f* : A -> B) × isEquiv A B f
--   | CEquiv Val Val

--   -- [P]  (n* : VNat) → P n → P (suc n)
--   | CNatElim Val

--   -- [A]  (B* : U) × equiv B A
--   | CEquivInto Val

  deriving Show

-- | Defunctionalized closures for IVar abstraction.
data IClosure
  = ICEval Sub Env Tm
  | ICCoePathP I I (BindI NamedIClosure) (BindI Val) (BindI Val) Val
  -- | ICHComPathP I I Name IClosure Val Val NeSys Val
  -- | ICConst Val
  -- | ICIsEquiv7 Val Val Val Val Val
  deriving Show

--------------------------------------------------------------------------------

rebind :: F (BindI a) -> b -> BindI b
rebind (F (BindI x i _)) b = BindI x i b
{-# inline rebind #-}

rebindf :: F (BindI a) -> b -> F (BindI b)
rebindf (F (BindI x i _)) b = F (BindI x i b)
{-# inline rebindf #-}

reclose :: NamedClosure -> (Closure -> Closure) -> NamedClosure
reclose (NCl x a) f = NCl x (f a)
{-# inline reclose #-}

packBindI2 :: BindI a -> BindI b -> BindI (a, b)
packBindI2 (BindI x i a) (BindI _ _ b) = BindI x i (a, b)
{-# inline packBindI2 #-}

unpackBindI2 :: BindI (a, b) -> (BindI a, BindI b)
unpackBindI2 (BindI x i (a, b)) = (BindI x i a, BindI x i b)
{-# inline unpackBindI2 #-}

packBindI3 :: BindI a -> BindI b -> BindI c -> BindI (a, b, c)
packBindI3 (BindI x i a) (BindI _ _ b) (BindI _ _ c) = BindI x i (a, b, c)
{-# inline packBindI3 #-}

unpackBindI3 :: BindI (a, b, c) -> (BindI a, BindI b, BindI c)
unpackBindI3 (BindI x i (a, b, c)) = (BindI x i a, BindI x i b, BindI x i c)
{-# inline unpackBindI3 #-}

-- Substitution
----------------------------------------------------------------------------------------------------

instance SubAction Val where
  sub = \case
    VSub v s' -> VSub v (sub s')
    v         -> VSub v ?sub

instance SubAction Ne where
  sub n = case n of
    NSub n s' -> NSub n (sub s')
    n         -> NSub n ?sub

instance SubAction NeSysSub where
  sub = \case
    NSSNe sys    -> NSSSub sys ?sub
    NSSSub sys s -> NSSSub sys (sub s)

instance SubAction NeSysHComSub where
  sub = \case
    NSHSNe sys    -> NSHSSub sys ?sub
    NSHSSub sys s -> NSHSSub sys (sub s)

instance SubAction Env where
  sub e = case e of
    ENil     -> ENil
    EDef e v -> EDef (sub e) (sub v)

instance SubAction a => SubAction (BindI a) where
  sub (BindI x i a) =
    let fresh = dom ?sub in
    let ?sub  = setCod i ?sub `ext` IVar fresh in
    BindI x fresh (sub a)
  {-# inline sub #-}

instance SubAction NamedClosure where
  sub (NCl x cl) = NCl x (sub cl)
  {-# inline sub #-}

instance SubAction NamedIClosure where
  sub (NICl x cl) = NICl x (sub cl)
  {-# inline sub #-}

instance SubAction Closure where
  sub cl = case cl of
    CEval s' env t ->
      CEval (sub s') (sub env) t

    -- note: recursive closure sub below! This is probably
    -- fine, because recursive depth is bounded by Pi type nesting.
    CCoePi r r' a b t ->
      CCoePi (sub r) (sub r') (sub a) (sub b) (sub t)

    CHComPi r r' a b sys base ->
      CHComPi (sub r) (sub r') (sub a) (sub b) (sub sys) (sub base)


    -- CConst t                  -> CConst (sub t)
    -- CIsEquiv1 a b f           -> CIsEquiv1 (sub a) (sub b) (sub f)
    -- CIsEquiv2 a b f g         -> CIsEquiv2 (sub a) (sub b) (sub f) (sub g)
    -- CIsEquiv3 a b f g linv    -> CIsEquiv3 (sub a) (sub b) (sub f) (sub g) (sub linv)
    -- CIsEquiv4 a f g           -> CIsEquiv4 (sub a) (sub f) (sub g)
    -- CIsEquiv5 b f g           -> CIsEquiv5 (sub b) (sub f) (sub g)
    -- CIsEquiv6 b f g linv rinv -> CIsEquiv6 (sub b) (sub f) (sub g) (sub linv) (sub rinv)
    -- CEquiv a b                -> CEquiv (sub a) (sub b)
    -- CNatElim p                -> CNatElim (sub p)
    -- CEquivInto a              -> CEquivInto (sub a)
    -- C'λ'a''a                  -> C'λ'a''a
    -- C'λ'a'i''a                -> C'λ'a'i''a
    -- C'λ'a'i'j''a              -> C'λ'a'i'j''a
    -- CCoeInv a r r'            -> CCoeInv   (sub a) (sub r) (sub r')
    -- CCoeLinv0 a r r'          -> CCoeLinv0 (sub a) (sub r) (sub r')
    -- CCoeRinv0 a r r'          -> CCoeRinv0 (sub a) (sub r) (sub r')

instance SubAction IClosure where
  sub cl = case cl of
    ICEval s' env t -> ICEval (sub s') (sub env) t

    -- -- recursive sub here as well!
    ICCoePathP r r' a lh rh p -> ICCoePathP (sub r) (sub r') (sub a) (sub lh) (sub rh) (sub p)

--     -- -- ICHComPathP r r' i a lhs rhs sys base ->
--     -- --   ICHComPathP (sub r) (sub r') i (sub a) (sub lhs) (sub rhs) (sub sys) (sub base)

--     -- ICConst t -> ICConst (sub t)

--     -- ICIsEquiv7 b f g linv x -> ICIsEquiv7 (sub b) (sub f) (sub g) (sub linv) (sub x)

--------------------------------------------------------------------------------

makeFields ''BindI
makeFields ''BindILazy
makeFields ''BindCof
makeFields ''BindCofLazy
makeFields ''NamedClosure
makeFields ''NamedIClosure
