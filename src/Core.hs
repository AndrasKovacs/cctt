{-# language UnboxedSums, UnboxedTuples #-}

module Core where

import Common
import Cube
import qualified LvlSet as LS


{-|
- We need to force w.r.t. a sub!
- Problem: double forcing + value weakening under cofs

  1. we can evaluate a term under a sub, which can store the sub in closures
  2. we can weaken the value to under an extended sub
     - in which case we want forcing to still make sense, and be idempotent!
     - stored sub update is *not necessarily* sub composition! It should be taking
       conjunction of cofibs instead! Is there an operational difference?

  There is some confusion of interval substitution and cofibrations

-}

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

  | GlueTy Ty System            -- Glue A [α ↦ B]      (B : Σ X (A ≃ X))
  | GlueTm Tm System            -- glue a [α ↦ b]
  | Unglue Tm System            -- unglue g [α ↦ B]    (B : Σ X (A ≃ X))
  deriving Show

data System
  = SEmpty
  | SCons Cof Tm System
  deriving Show

--------------------------------------------------------------------------------

data VSystem
  = VSEmpty
  | VSCons Cof ~Val VSystem

data Ne
  = NLocalVar Lvl
  | NApp Ne Val
  | NPApp Val Val Ne IVar
  | NProj1 Ne
  | NProj2 Ne
  | NCoe I I Name VTy Val
  | NHCom I I Name VTy VSystem Val
  | NGlueTy VTy VSystem
  | NUnglue Val VSystem

data Env
  = ENil
  | EDef Env ~Val

type EnvArg = (?env :: Env)

data Closure
  = CEval Env Sub Tm

type VTy = Val

-- set of blocking ivars, delayed sub
data NeForcing = NeForcing LS.LvlSet Sub

addBlockingIVar :: IVar -> NeForcing -> NeForcing
addBlockingIVar x (NeForcing is s) = NeForcing (LS.insert (coerce x) is) s

data Val
  = VNe Ne NeForcing
  | VSub Val Sub
  | VPi Name VTy Closure
  | VLam Name Closure
  | VPathP Name Closure Val Val
  | VPLam Name Closure
  | VSg Name VTy Closure
  | VPair Val Val
  | VU

localVar :: EnvArg => Ix -> Val
localVar x = go ?env x where
  go (EDef _ v) 0 = v
  go (EDef e _) x = go e (x - 1)
  go _          _ = impossible

capp :: LvlArg => Closure -> Val -> Val
capp t u = case t of
  CEval e s t -> let ?env = EDef e u; ?sub = s in eval t

cpapp :: LvlArg => Closure -> I -> Val
cpapp t i = case t of
  CEval e s t -> let ?env = e; ?sub = snocSub s i in eval t

instance SubAction Val where
  sub v s = case v of
    VSub v s' -> VSub v (sub s' s)
    v         -> VSub v s

instance SubAction Closure where
  sub cl s = case cl of
    CEval e s' t -> CEval (sub e s) (sub s' s) t

instance SubAction Env where
  sub e s = case e of
    ENil     -> ENil
    EDef e v -> EDef (sub e s) (sub v s)

-- forceNe :: LvlArg => Ne -> NeForcing -> Sub -> Val
-- forceNe n (NeForcing is s') s =
--   let s'' = sub s' s
--   in _

-- force' :: LvlArg => Sub -> Val -> Val
-- force' s = \case
--   VNe n frc      -> forceNe n frc s
--   VSub v s'      -> force' (sub s' s) v
--   VPi x a b      -> VPi x (sub a s) (sub b s)
--   VLam x t       -> VLam x (sub t s)
--   VPathP x a t u -> VPathP x (sub a s) (sub t s) (sub u s)
--   VPLam x t      -> VPLam x (sub t s)
--   VSg x a b      -> VSg x (sub a s) (sub b s)
--   VPair t u      -> VPair (sub t s) (sub u s)
--   VU             -> VU
-- {-# noinline force' #-}


force' :: LvlArg => SubArg => Val -> Val
force' = \case
  VNe n frc      -> _


  VSub v s'      -> let ?sub = sub s' ?sub in force' v
  VPi x a b      -> VPi x (sub a ?sub) (sub b ?sub)
  VLam x t       -> VLam x (sub t ?sub)
  VPathP x a t u -> VPathP x (sub a ?sub) (sub t ?sub) (sub u ?sub)
  VPLam x t      -> VPLam x (sub t ?sub)
  VSg x a b      -> VSg x (sub a ?sub) (sub b ?sub)
  VPair t u      -> VPair (sub t ?sub) (sub u ?sub)
  VU             -> VU
{-# noinline force' #-}

force :: LvlArg => SubArg => Val -> Val
force = \case
  VSub v s -> let ?sub = sub s ?sub in force' v
  v        -> v
{-# inline force #-}

app :: LvlArg => Val -> Val -> Val
app t u = case t of
  VLam _ t  -> capp t u
  VNe t frc -> VNe (NApp t u) frc
  _         -> impossible

papp :: LvlArg => Val -> Val -> Val -> I -> Val
papp ~t ~u0 ~u1 i = case i of
  I0     -> u0
  I1     -> u1
  IVar x -> case t of
    VPLam _ t -> cpapp t (IVar x)
    VNe t frc -> VNe (NPApp u0 u1 t x) (addBlockingIVar x frc)
    _         -> impossible
{-# inline papp #-}

proj1 :: Val -> Val
proj1 t = case t of
  VPair t _ -> t
  VNe t frc -> VNe (NProj1 t) frc
  _         -> impossible

proj2 :: Val -> Val
proj2 t = case t of
  VPair _ u -> u
  VNe t frc -> VNe (NProj2 t) frc
  _         -> impossible

eval :: LvlArg => EnvArg => SubArg => Tm -> Val
eval = \case
  TopVar _ v     -> coerce v
  LocalVar x     -> localVar x
  Let x _ t u    -> let ~v = eval t in let ?env = EDef ?env v in eval u
  Pi x a b       -> VPi x (eval a) (CEval ?env ?sub b)
  App t u        -> app (eval t) (eval u)
  Lam x t        -> VLam x (CEval ?env ?sub t)
  Sg x a b       -> VSg x (eval a) (CEval ?env ?sub b)
  Pair t u       -> VPair (eval t) (eval u)
  Proj1 t        -> proj1 (eval t)
  Proj2 t        -> proj2 (eval t)
  U              -> VU
  PathP x a t u  -> VPathP x (CEval ?env ?sub a) (eval t) (eval u)
  PApp t u0 u1 i -> papp (eval t) (eval u0) (eval u1) (sub i ?sub)
  PLam x t       -> VPLam x (CEval ?env ?sub t)

-- cof :: Sub -> Cof -> UpdSub
-- cof s CTrue = USTrue
-- cof s (CAnd (CofEq x i) phi) = case cof s phi of
--   USFalse -> USFalse
--   USTrue -> case updSub (CofEq x i) s of
--     USTrue     -> USTrue
--     USFalse    -> USFalse
--     USUpdate s -> USUpdate s
--   USUpdate s -> case updSub (CofEq x i) s of
--     USTrue     -> USUpdate s
--     USFalse    -> USFalse
--     USUpdate s -> USUpdate s
