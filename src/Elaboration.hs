{-# options_ghc -Wno-unused-imports #-}

module Elaboration where

import qualified Data.Map.Strict as M
import Text.Megaparsec (SourcePos)
import Control.Exception

import Common
import Conversion
import Core hiding (bind, bindI, eval, evalf)
import Interval
import Substitution

import qualified IVarSet   as IS
import qualified Presyntax as P
import qualified Core

--------------------------------------------------------------------------------

eval :: IDomArg => NCofArg => DomArg => EnvArg => Tm -> Val
eval = uf


-- Context
--------------------------------------------------------------------------------

data Entry
  = Top Lvl VTy ~Val      -- level, type, value
  | Local Lvl VTy         -- level, type
  | LocalInt IVar

type TableArg = (?tbl    :: M.Map Name Entry)
type PosArg   = (?srcPos :: SourcePos)

type Elab a = IDomArg => NCofArg => DomArg => EnvArg => TableArg => PosArg => a

bind :: Name -> VTy -> Elab (Val -> a) -> Elab a
bind x a act =
  let v    = vVar ?dom in
  let ?dom = ?dom + 1
      ?env = EDef ?env v
      ?tbl = M.insert x (Local ?dom a) ?tbl in
  let _ = ?dom; _ = ?env; _ = ?tbl in
  act v
{-# inline bind #-}

define :: Name -> VTy -> Val -> Elab a -> Elab a
define x a ~v act =
  let ?env = EDef ?env v
      ?tbl = M.insert x (Local ?dom a) ?tbl in
  let _ = ?env; _ = ?tbl in
  act
{-# inline define #-}

bindI :: Name -> Elab (IVar -> a) -> Elab a
bindI x act =
  let fresh = ?idom in
  let ?idom = ?idom + 1
      ?cof  = extSub ?cof (IVar ?idom)
      ?tbl  = M.insert x (LocalInt fresh) ?tbl in
  act fresh
{-# inline bindI #-}

-- Errors
--------------------------------------------------------------------------------

data Error
  = NameNotInScope Name
  | UnexpectedInt
  | ExpectedPi
  | ExpectedSg
  | CantInferLam
  | CantInferPair
  deriving Show

instance Exception Error where

data ErrInCxt = ErrInCxt SourcePos Error
  deriving Show

instance Exception ErrInCxt where

err :: PosArg => Error -> IO a
err e = throwIO $ ErrInCxt ?srcPos e

--------------------------------------------------------------------------------

data Infer = Infer Tm ~VTy

check :: Elab (P.Tm -> VTy -> IO Tm)
check = uf

checkU :: Elab (P.Tm -> IO Tm)
checkU = uf

checkI :: Elab (P.Tm -> IO I)
checkI = uf

infer :: Elab (P.Tm -> IO Infer)
infer = \case
  P.Ident x -> case M.lookup x ?tbl of
    Nothing -> err $ NameNotInScope x
    Just e  -> case e of
      Top l a v  -> pure $! Infer (TopVar l (DontShow v)) a
      Local l a  -> pure $! Infer (LocalVar (lvlToIx ?dom l)) a
      LocalInt l -> err UnexpectedInt

  P.Pos pos t -> let ?srcPos = coerce pos in infer t

  P.Let x Nothing t u -> do
    Infer t a <- infer t
    let ~vt = eval t
    define x a vt $ infer u

  P.Let x (Just a) t u -> do
    a <- checkU a
    let va = eval a
    t <- check t va
    let ~vt = eval t
    define x va vt $ infer u

  P.Pi x a b -> do
    a <- checkU a
    b <- bind x (eval a) \_ -> checkU b
    pure $ Infer (Pi x a b) VU

  P.App t u -> do
    Infer t a <- infer t
    case unF (force a) of
      VPi x a b -> do
        u <- check u a
        pure $! Infer (App t u) (capp b (eval u))
      VPathP x a l r -> do
        u <- checkI u
        uf
        -- pure $! Infer (PApp (quote l) (quote r) t u) (icapp a (unF (evalI u)))
      _ ->
        err ExpectedPi

  P.Lam{} ->
    err CantInferLam

  P.Sg x a b -> do
    a <- checkU a
    b <- bind x (eval a) \_ -> checkU b
    pure $ Infer (Sg x a b) VU

  P.Pair{} ->
    err CantInferPair

  P.Proj1 t -> do
    Infer t a <- infer t
    case unF (force a) of
      VSg x a b -> do
        pure $ Infer (Proj1 t) a
      _ ->
        err ExpectedSg

  P.Proj2 t -> do
    Infer t a <- infer t
    case unF (force a) of
      VSg x a b -> do
        uf
        -- pure $! Infer (Proj2 t) (capp b (proj1 (evalf t)))
      _ ->
        err ExpectedSg

  P.U ->
    pure $ Infer U VU

  P.Path t u -> do
    Infer t a <- infer t
    u <- check u a
    pure $ Infer (PathP "_" (Core.bindI \_ -> quote a) t u) VU

  P.Coe r r' x a t -> do
    r  <- checkI r
    r' <- checkI r'
    a  <- bindI x \_ -> checkU a
    uf
    -- t  <- check t (evalTopSub a (evalI r))
    -- pure $ Infer (Coe r r' x a t) (evalTopSub a (evalI r'))

  -- P.HCom !P.I !P.I !Name !P.Ty !P.System !P.Tm
  -- P.GlueTy !P.Ty !P.System
  -- P.GlueTm !P.Tm
  -- P.Unglue !P.Tm
  -- P.Nat
  -- P.Zero
  -- P.Suc !P.Tm
  -- P.NatElim !P.Tm !P.Tm !P.Tm !P.Tm

-- TODO: forcing in elab which checks for subAction!
