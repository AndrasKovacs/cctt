
module Presyntax where

import Common
import Text.Megaparsec (SourcePos)

type Ty = Tm

data Tm
  = Ident Name
  | Pos (DontShow SourcePos) Tm
  | I0
  | I1
  | Let Name (Maybe Ty) Tm Tm
  | Pi Name Ty Ty
  | App Tm Tm
  | Lam Name Tm
  | Sg Name Ty Ty
  | Pair Tm Tm
  | Proj1 Tm
  | Proj2 Tm
  | U
  | Path Tm Tm                    -- PathP _   x y
  | PathP Name Ty Tm Tm           -- PathP i.A x y

  | Coe Tm Tm Name Ty Tm          -- coe r r' i.A t
  | HCom Tm Tm Name Ty System Tm  -- hcom r r' i.A [α → t] u

  | GlueTy Ty System              -- Glue A [α ↦ B]      (B : Σ X (X ≃ A))
  | GlueTm Tm
  | Unglue Tm

  | Nat
  | Zero
  | Suc Tm
  | NatElim Tm Tm Tm Tm         -- (P : Nat -> U) -> P z -> ((n:_) -> P n -> P (suc n)) -> (n:_) -> P n
  deriving Show

data CofEq = CofEq Tm Tm
  deriving Show

data Cof = CTrue | CAnd {-# unpack #-} CofEq Cof
  deriving Show

data System = SEmpty | SCons Cof Tm System
  deriving Show

data Top = TDef Name (Maybe Ty) Tm Top
         | TEmpty
  deriving Show
