
module Presyntax where

import Common
import Text.Megaparsec (SourcePos)

type Ty = Tm

data Tm
  = Ident Name
  | Pos (DontShow SourcePos) Tm
  | I
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
  | Path (Maybe Ty) Tm Tm             -- x ={A} y
  | PathP Name Ty Tm Tm               -- x ={i.A} y

  | Coe Tm Tm Name Ty Tm              -- coe r r' i A t
  | HCom Tm Tm (Maybe Ty) SysHCom Tm  -- hcom r r' A [α x. t] u
  | Com Tm Tm Name Ty SysHCom Tm      -- com r r' i A [α x. t] u

  | GlueTy Ty Sys                     -- Glue A [α. B]      (B : Σ X (X ≃ A))
  | GlueTm Tm Sys                     -- glue a [α. t]
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

data Sys = SEmpty | SCons Cof Tm Sys
  deriving Show

data SysHCom = SHEmpty | SHCons Cof Name Tm SysHCom
  deriving Show

data Top = TDef (DontShow SourcePos) Name (Maybe Ty) Tm Top | TEmpty
  deriving Show

unPos :: Tm -> Tm
unPos (Pos _ a) = a
unPos a         = a
{-# inline unPos #-}
