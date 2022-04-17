
{-# language Strict, LambdaCase, BangPatterns, ViewPatterns #-}

type Name = String

data ITm = IVar Int | IZero | IOne deriving Show

data Cof = COr Cof Cof | CAll Name Cof | CEq ITm ITm deriving Show

data System = SEmpty | SCons ITm ITm Tm System deriving Show

type Ty = Tm

data Tm
  = LocalVar Int
  | Let Name Ty Tm Tm

  | Pi Name Tm Tm
  | App Tm Tm
  | Lam Name Tm

  | Univ

  | Path Name Ty Tm Tm
  | LamP Name Tm
  | AppP Tm Tm Tm ITm
  | Coe Name ITm ITm Ty Tm
  | HCom Name ITm ITm Ty System Tm
  deriving Show

{-
Plan:
- delayed interval subst, no interval closures, eager subst composition,
  no interval vals
- closures & values for ordinary values
- glued eval for top defs, also probably useful for interval subst (because top defs are closed)
- probably we need fresh vars and disjoint subst for intervals

- we need to restrart reductions of neutrals on interval subst
- how to represent blocked eval?
  * problem is that some things can block on multiple things:
     - AppP : path & arg
     - hcom : src/tgt & system
  * only definitely non-Ivar-headed neutrals are stable under I-subst

  * for efficient forcing we definitely need to gather up *all* possible blocking
    points in neutrals!

    E.g. take a spine which has a path application *anywhere* inside. Then
    if the outermost path application is forced by 0/1 arg, all inner blocking
    points are just dropped!


-}

type VTy = Val

data Head
data Spine

data Val =
  VNe Head Spine




  -- = VVar Int

  -- | VPi Name Val Val
  -- | VApp Val Val
  -- | VLam Name Val

  -- | VUniv

  -- | VPath Name Ty Val Val
  -- | VLamP Name Val
  -- | VAppP Val Val Val ITm

  -- | VCofSplit Cof Val Cof Val
  -- | VCoe Name ITm ITm Ty Val
  -- | VHCom Name ITm ITm Ty Cof Val Val
  -- deriving Show
