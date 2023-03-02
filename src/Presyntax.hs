
module Presyntax where

import Common
import Text.Megaparsec (SourcePos)

type Ty = Tm

data Tm
  = Ident Name
  | LocalLvl Lvl                  -- @n
  | TopLvl Lvl                    -- @@n
  | Pos (DontShow SourcePos) Tm
  | I
  | ILvl IVar
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
  | Path Tm Tm                          -- x = y
  | DepPath BindMaybe Tm Tm             -- x ={i.A} y | x ={p} y

  | Coe Tm Tm BindMaybe Tm              -- coe r r' i A t
  | HCom Tm Tm (Maybe Ty) SysHCom Tm    -- hcom r r' A [α x. t] u
  | Com Tm Tm BindMaybe SysHCom Tm      -- com r r' i A [α x. t] u

  | GlueTy Ty Sys                     -- Glue A [α. B]      (B : Σ X (X ≃ A))
  | GlueTm Tm Sys                     -- glue a [α. t]
  | Unglue Tm

  | Nat
  | Zero
  | Suc Tm
  | NatElim Tm Tm Tm Tm         -- (P : Nat -> U) -> P z -> ((n:_) -> P n -> P (suc n)) -> (n:_) -> P n

  | Refl          -- checkable refl
  | Sym Tm
  | Trans Tm Tm
  | Ap Tm Tm
  deriving Show

data CofEq = CofEq Tm Tm
  deriving Show

data Cof = CTrue | CAnd {-# unpack #-} CofEq Cof
  deriving Show

data Sys = SEmpty | SCons Cof Tm Sys
  deriving Show

data BindMaybe = Bind Name Tm | DontBind Tm
  deriving Show

data SysHCom = SHEmpty | SHCons Cof BindMaybe SysHCom
  deriving Show

data Top = TDef (DontShow SourcePos) Name (Maybe Ty) Tm Top | TEmpty
  deriving Show

unPos :: Tm -> Tm
unPos (Pos _ a) = a
unPos a         = a
{-# inline unPos #-}
