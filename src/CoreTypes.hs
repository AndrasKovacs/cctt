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

type VTy = Val

data Val
  = VSub Val Sub

  -- Neutrals. These are annotated with sets of blocking ivars. Glue types are
  -- also neutral, but they're handled separately, because we have to match on
  -- them in coe/hcom.
  | VNe Ne IS.IVarSet

  | VGlueTy VTy NeSys'

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

data Ne
  = NLocalVar Lvl
  | NSub Ne Sub
  | NApp Ne Val
  | NPApp Ne ~Val ~Val I
  | NProj1 Ne
  | NProj2 Ne
  | NCoe I I Name (Bind Val) Val
  | NHCom I I Name VTy NeSysBind Val
  | NUnglue Val NeSys
  | NGlue Val NeSys
  | NNatElim Val Val Val Ne
  deriving Show

--------------------------------------------------------------------------------

vVar :: Lvl -> Val
vVar x = VNe (NLocalVar x) mempty
{-# inline vVar #-}

newtype F a = F {unF :: a}
  deriving SubAction via a

type DomArg = (?dom :: Lvl)    -- fresh LocalVar

--------------------------------------------------------------------------------

-- | Defunctionalized closures.
data Closure
  -- ^ Body of vanilla term evaluation.
  = CEval Sub Env Tm

  -- ^ Body of function coercions.
  | CCoePi I I (Bind (VTy, Closure)) Val

  -- ^ Body of function hcom.
  | CHComPi I I VTy Closure NeSysBind Val

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
  | ICCoePathP I I (Bind (IClosure, Val, Val)) Val
  -- | ICHComPathP I I Name IClosure Val Val NeSys Val
  -- | ICConst Val
  -- | ICIsEquiv7 Val Val Val Val Val
  deriving Show

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

data Env
  = ENil
  | EDef Env ~Val
  deriving Show

type EnvArg = (?env :: Env)

data Bind a = Bind {
    bindName  :: Name
  , bindBinds :: IVar
  , bindBody  :: a}
  deriving Show

rebind :: F (Bind a) -> b -> Bind b
rebind (F (Bind x i _)) b = Bind x i b
{-# inline rebind #-}

rebindf :: F (Bind a) -> b -> F (Bind b)
rebindf (F (Bind x i _)) b = F (Bind x i b)
{-# inline rebindf #-}

packBind2 :: Bind a -> Bind b -> Bind (a, b)
packBind2 (Bind x i a) (Bind _ _ b) = Bind x i (a, b)
{-# inline packBind2 #-}

unpackBind2 :: Bind (a, b) -> (Bind a, Bind b)
unpackBind2 (Bind x i (a, b)) = (Bind x i a, Bind x i b)
{-# inline unpackBind2 #-}

packBind3 :: Bind a -> Bind b -> Bind c -> Bind (a, b, c)
packBind3 (Bind x i a) (Bind _ _ b) (Bind _ _ c) = Bind x i (a, b, c)
{-# inline packBind3 #-}

unpackBind3 :: Bind (a, b, c) -> (Bind a, Bind b, Bind c)
unpackBind3 (Bind x i (a, b, c)) = (Bind x i a, Bind x i b, Bind x i c)
{-# inline unpackBind3 #-}

inst :: SubAction a => NCofArg => Bind a -> I -> a
inst (Bind x i a) j =
  let s = setCod i (idSub (dom ?cof)) `ext` j
  in doSub s a
{-# inline inst #-}

data BindLazy a = BindLazy  {
    bindLazyName  :: Name
  , bindLazyBinds :: IVar
  , bindLazyBody  :: ~a}
  deriving Show

rebindLazy :: BindLazy a -> b -> BindLazy b
rebindLazy (BindLazy x i _) ~b = BindLazy x i b
{-# inline rebindLazy #-}

instLazy :: SubAction a => NCofArg => BindLazy a -> I -> a
instLazy (BindLazy x i a) j =
  let s = setCod i (idSub (dom ?cof)) `ext` j
  in doSub s a
{-# inline instLazy #-}

data NeSys
  = NSEmpty
  | NSCons NeCof ~Val NeSys
  deriving Show

data NeSys' = NeSys' {
    neSys'Nsys  :: NeSys
  , neSys'Ivars :: IS.IVarSet
  } deriving Show

-- TODO: unbox
data VSys
  = VSTotal ~Val
  | VSNe NeSys'
  deriving Show

data NeSysBind
  = NSBEmpty
  | NSBCons NeCof (BindLazy Val) NeSysBind
  deriving Show

data NeSysBind' = NeSysBind' {
     neSysBind'Nsys  :: NeSysBind
  ,  neSysBind'Ivars :: IS.IVarSet
  } deriving Show

-- TODO: unbox
data VSysBind
  = VSBTotal (BindLazy Val)
  | VSBNe NeSysBind'
  deriving Show


-- Substitution
----------------------------------------------------------------------------------------------------

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

instance SubAction NeSys where
  sub sys = case sys of
    NSEmpty          -> NSEmpty
    NSCons cof v sys -> NSCons (sub cof) (sub v) (sub sys)

instance SubAction NeSys' where
  sub (NeSys' nsys is) = NeSys' (sub nsys) (sub is)

instance SubAction VSys where
  sub sys = case sys of
    VSTotal v  -> VSTotal (sub v)
    VSNe nsys  -> VSNe (sub nsys)

instance SubAction Ne where
  sub n = case n of
    NSub n s' -> NSub n (sub s')
    n         -> NSub n ?sub

instance SubAction Env where
  sub e = case e of
    ENil     -> ENil
    EDef e v -> EDef (sub e) (sub v)

instance SubAction a => SubAction (Bind a) where
  sub (Bind x i a) =
    let fresh = dom ?sub in
    let ?sub  = setCod i ?sub `ext` IVar fresh in
    Bind x fresh (sub a)
  {-# inline sub #-}

instance SubAction a => SubAction (BindLazy a) where
  sub (BindLazy x i a) =
    let fresh = dom ?sub in
    let ?sub  = setCod i ?sub `ext` IVar fresh in
    BindLazy x fresh (sub a)
  {-# inline sub #-}

instance SubAction NeSysBind where
  sub = \case
    NSBEmpty -> NSBEmpty
    NSBCons cof t sys -> uf

instance SubAction Closure where
  sub cl = case cl of
    CEval s' env t ->
      CEval (sub s') (sub env) t

    -- note: recursive closure sub below! This is probably
    -- fine, because recursive depth is bounded by Pi type nesting.
    CCoePi r r' ab t ->
      CCoePi (sub r) (sub r') (sub ab) (sub t)

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

    -- recursive sub here as well!
    ICCoePathP r r' alr p -> ICCoePathP (sub r) (sub r') (sub alr) (sub p)

--     -- -- ICHComPathP r r' i a lhs rhs sys base ->
--     -- --   ICHComPathP (sub r) (sub r') i (sub a) (sub lhs) (sub rhs) (sub sys) (sub base)

--     -- ICConst t -> ICConst (sub t)

--     -- ICIsEquiv7 b f g linv x -> ICIsEquiv7 (sub b) (sub f) (sub g) (sub linv) (sub x)

--------------------------------------------------------------------------------

makeFields ''NeSysBind'
makeFields ''NeSys'
makeFields ''Bind
makeFields ''BindLazy
