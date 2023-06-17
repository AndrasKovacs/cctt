{-# options_ghc -funbox-strict-fields #-}

module Presyntax where

import Common hiding (Name)

type Ty = Tm
type Name = Span

data Bind
  = BName Name
  | BDontBind Pos
  deriving Show

data LamAnnot
  = LANone
  | LAAnn Ty
  | LADesugared Ty
  deriving Show

data Tm
  = Ident Name
  | LocalLvl Pos Lvl Pos
  | TopLvl Pos Lvl (Maybe Lvl) Pos   -- @@n   or   @@n.m    (the latter identifies a data constructor)
  | I Pos
  | ILvl Pos IVar Pos
  | I0 Pos
  | I1 Pos
  | Let Pos Name (Maybe Ty) Tm Tm
  | Pi Pos Bind Ty Ty
  | App Tm Tm
  | PApp Pos Tm Tm Tm Tm        -- explicit endpoints: t {l}{r} u
  | Lam Pos Bind LamAnnot Tm
  | PLam Pos Tm Tm Bind Tm      -- explicit endpoints: λ {l}{r} x. t

  | Parens Pos Tm Pos

  | Sg Pos Bind Ty Ty
  | Pair Tm Tm
  | Proj1 Tm Pos
  | Proj2 Tm Pos
  | ProjField Tm Name

  | Wrap Pos Bind Ty Pos
  | Hole Pos (Maybe Bind)

  | Case Pos Tm (Maybe (Bind, Ty)) [CaseItem] Pos
  | Split Pos [CaseItem] Pos

  | U Pos
  | Path Tm Tm                                -- x = y
  | DepPath BindMaybe Tm Tm                   -- x ={i.A} y | x ={p} y

  | Coe Pos Tm Tm BindMaybe Tm                    -- coe r r' i A t
  | HCom Pos Tm Tm (Maybe Ty) SysHCom Tm          -- hcom r r' {A} [α x. t] u
  | Com Pos Tm Tm BindMaybe SysHCom Tm            -- com r r' i A [α x. t] u

  | GlueTy Pos Ty Sys Pos                             -- Glue A [α. B]
  | GlueTm Pos Tm (Maybe Sys) Sys Pos                 -- glue a {<equivsys>} <fibersys>
  | Unglue Pos Tm

  | Refl Pos Pos
  | Sym Tm Pos
  | Trans Tm Tm
  | Ap Pos Tm Tm
  deriving Show

data Cof = CEq Tm Tm
  deriving Show

data Sys = SEmpty | SCons Cof Tm Sys
  deriving Show

data BindMaybe = BMBind Bind Tm | BMDontBind Tm
  deriving Show

data SysHCom = SHEmpty | SHCons Pos Cof BindMaybe SysHCom
  deriving Show

type Constructor = (Name, [(Bind, Ty)])
type HConstructor = (Name, [(Bind, Ty)], Maybe Sys)
type CaseItem = (Bind, [Bind], Tm)

data Top
  = TDef    Pos Name (Maybe Ty) Tm Top
  | TData   Pos Name [(Bind, Ty)] [Constructor] Top
  | THData  Pos Name [(Bind, Ty)] [HConstructor] Top
  | TImport Pos String Top
  | TEmpty
  deriving Show

class Spanned a where
  spanOf :: a -> Span
  spanOf a = Span (leftPos a) (rightPos a)

  leftPos :: a -> Pos
  leftPos a = case spanOf a of Span p _ -> p

  rightPos :: a -> Pos
  rightPos a = case spanOf a of Span _ p -> p

instance Spanned Bind where
  spanOf (BDontBind p) = Span p p
  spanOf (BName x)     = x

instance Spanned Name where
  spanOf x = x

instance Spanned Tm where
  leftPos = \case
     Ident x          -> leftPos x
     LocalLvl l _ _   -> l
     TopLvl l _ _ _   -> l
     I l              -> l
     ILvl l _ _       -> l
     I0 l             -> l
     I1 l             -> l
     Let l _ _ _ _    -> l
     Pi l _ _ _       -> l
     App t _          -> leftPos t
     PApp l _ _ _ _   -> l
     Lam l _ _ _      -> l
     PLam l _ _ _ _   -> l
     Parens l _ _     -> l
     Sg l _ _ _       -> l
     Pair t _         -> leftPos t
     Proj1 t _        -> leftPos t
     Proj2 t _        -> leftPos t
     ProjField t _    -> leftPos t
     Wrap l _ _ _     -> l
     Hole l _         -> l
     Case l _ _ _ _   -> l
     Split l _ _      -> l
     U l              -> l
     Path t _         -> leftPos t
     DepPath _ t _    -> leftPos t
     Coe l _ _ _ _    -> l
     HCom l _ _ _ _ _ -> l
     Com l _ _ _ _ _  -> l
     GlueTy l _ _ _   -> l
     GlueTm l _ _ _ _ -> l
     Unglue l _       -> l
     Refl l _         -> l
     Sym t _          -> leftPos t
     Trans t _        -> leftPos t
     Ap l _ _         -> l

  rightPos = \case
     Ident x          -> rightPos x
     LocalLvl _ _ r   -> r
     TopLvl _ _ _ r   -> r
     I r              -> r
     ILvl _ _ r       -> r
     I0 r             -> r
     I1 r             -> r
     Let _ _ _ _ u    -> rightPos u
     Pi _ _ _ b       -> rightPos b
     App _ t          -> rightPos t
     PApp _ _ _ _ t   -> rightPos t
     Lam _ _ _ t      -> rightPos t
     PLam _ _ _ _ t   -> rightPos t
     Parens _ _ r     -> r
     Sg _ _ _ b       -> rightPos b
     Pair _ t         -> rightPos t
     Proj1 _ r        -> r
     Proj2 _ r        -> r
     ProjField _ r    -> rightPos r
     Wrap _ _ _ r     -> r
     Hole p x         -> maybe p rightPos x
     Case _ _ _ _ r   -> r
     Split _ _ r      -> r
     U r              -> r
     Path _ t         -> rightPos t
     DepPath _ _ t    -> rightPos t
     Coe _ _ _ _ t    -> rightPos t
     HCom _ _ _ _ _ t -> rightPos t
     Com _ _ _ _ _ t  -> rightPos t
     GlueTy _ _ _ r   -> r
     GlueTm _ _ _ _ r -> r
     Unglue _ t       -> rightPos t
     Refl _ r         -> r
     Sym _ r          -> r
     Trans _ t        -> rightPos t
     Ap _ _ t         -> rightPos t

instance (Spanned a, Spanned b) => Spanned (a, b) where
  leftPos (x, y) = leftPos x
  rightPos (x, y) = rightPos y

instance Spanned Pos where
  leftPos x = x
  rightPos x = x

instance (Spanned a, Spanned b, Spanned c) => Spanned (a, b, c) where
  leftPos (x, y, z) = leftPos x
  rightPos (x, y, z) = rightPos z

instance Spanned a => Spanned [a] where
  leftPos []      = impossible
  leftPos (x:_)   = leftPos x
  rightPos []     = impossible
  rightPos [x]    = rightPos x
  rightPos (_:xs) = rightPos xs

instance Spanned BindMaybe where
  leftPos  (BMBind x t)   = leftPos x
  leftPos  (BMDontBind t) = leftPos t
  rightPos (BMBind x t)   = rightPos t
  rightPos (BMDontBind t) = rightPos t

instance Spanned Cof where
  leftPos  (CEq t _) = leftPos t
  rightPos (CEq _ t) = rightPos t

unParens :: Tm -> Tm
unParens (Parens _ t _) = unParens t
unParens t              = t
