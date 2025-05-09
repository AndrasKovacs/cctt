{-# options_ghc -funbox-strict-fields -Wno-orphans #-}

module CoreTypes where

import Common
import Cubical

import qualified Data.LvlMap as LM

-- Syntax
--------------------------------------------------------------------------------

data RecInfo = RI {
    recInfoRecId    :: Lvl
  , recInfoRecTy    :: ~Ty
  , recInfoRecTyVal :: ~VTy
  , recInfoName     :: Name
  , recInfoPos      :: Pos
  }

instance Show RecInfo where
  show (RI _ _ _ x _) = show x

data DefInfo = DI {
    defInfoDefId     :: Lvl
  , defInfoDef       :: Tm
  , defInfoDefVal    :: ~Val
  , defInfoDefTy     :: ~Ty
  , defInfoDefTyVal  :: ~VTy
  , defInfoName      :: Name
  , defInfoPos       :: Pos
  , defInfoUnfolding :: Bool
  }

instance Show DefInfo where
  show (DI _ _ _ _ _ x _ _) = show x

data TyConInfo = TCI {
    tyConInfoTyId         :: Lvl
  , tyConInfoParamTypes   :: Tel
  , tyConInfoConstructors :: IORef (LM.Map DConInfo)
  , tyConInfoFrozen       :: IORef Bool
  , tyConInfoName         :: Name
  , tyConInfoPos          :: Pos
  }

instance Show TyConInfo where
  show (TCI _ _ _ _ x _) = show x

data DConInfo = DCI {
    dConInfoConId      :: Lvl
  , dConInfoFieldTypes :: Tel
  , dConInfoName       :: Name
  , dConInfoTyConInfo  :: {-# nounpack #-} TyConInfo
  , dConInfoPos        :: Pos
  }

instance Show DConInfo where
  show (DCI _ _ x _ _) = show x

data HDConInfo = HDCI {
    hDConInfoConId      :: Lvl
  , hDConInfoFieldTypes :: Tel
  , hDConInfoIsCoherent :: Bool
  , hDConInfoIfields    :: [Name]
  , hDConInfoBoundary   :: Sys
  , hDConInfoName       :: Name
  , hDConInfoTyConInfo  :: {-# nounpack #-} HTyConInfo
  , hDConInfoPos        :: Pos
  }

instance Show HDConInfo where
  show (HDCI _ _ _ _ _ x _ _) = show x

data HTyConInfo = HTCI {
    hTyConInfoTyId         :: Lvl
  , hTyConInfoParamTypes   :: Tel
  , hTyConInfoConstructors :: IORef (LM.Map HDConInfo)
  , hTyConInfoFrozen       :: IORef Bool
  , hTyConInfoName         :: Name
  , hTyConInfoPos          :: Pos
  }

instance Show HTyConInfo where
  show (HTCI _ _ _ _ x _) = show x

--------------------------------------------------------------------------------

type Ty = Tm
type CaseTag = Int

data Tel
  = TNil
  | TCons Name Ty Tel
  deriving Show

data Spine
  = SPNil
  | SPCons Tm Spine
  deriving Show

data LazySpine
  = LSPNil
  | LSPCons ~Tm LazySpine
  deriving Show

data PrintTrace = PrintTrace | DontPrintTrace
  deriving Show

data Tm
  = TopVar        {-# nounpack #-} DefInfo PrintTrace
  | RecursiveCall {-# nounpack #-} RecInfo
  | LocalVar Ix
  | Let Name ~Ty Tm Tm

  | TyCon {-# nounpack #-} TyConInfo Spine
  | DCon  {-# nounpack #-} DConInfo  Spine

  | HTyCon {-# nounpack #-} HTyConInfo Spine

  -- LazySpine is for params which are usually quoted from syntax and we want
  -- to avoid computing them.
  -- Sub is the spine of interval args in a HDCon.
  | HDCon {-# nounpack #-} HDConInfo LazySpine Spine Sub

  | HCase Tm Name ~Ty HCases
  | HSplit Name ~Ty HCases

  | Case Tm Name ~Ty Cases
  | Split Name ~Ty Cases

  | Pi Name Ty Ty
  | App Tm Tm
  | Lam Name Tm

  | Sg Name Ty Ty
  | Pair Name Tm Tm
  | Proj1 Tm Name
  | Proj2 Tm Name

  | Wrap Name Ty
  | Pack Name Tm
  | Unpack Tm Name

  | U

  | Path Name ~Ty Tm Tm    -- x ={i. a} y
  | PApp ~Tm ~Tm Tm I      -- (x : A 0)(y : A 1)(t : x ={i.A i} y)(j : I)
  | PLam ~Tm ~Tm Name Tm   -- endpoints, body

  | Line Name Tm           -- (i : I) → A
  | LApp Tm I
  | LLam Name Tm

  | Coe I I Name Ty Tm      -- coe r r' i.A t
  | HCom I I ~Ty SysHCom Tm  -- hcom r r' i A [α → t] u

  -- we switch the field orders here compared to the papers, because
  -- this one is the sensible "dependency" order
  | GlueTy Ty Sys            -- Glue A [α ↦ B]      (B : Σ X (X ≃ A))
  | Glue   Tm ~Sys ~Sys      -- glue a <equiv> <fib>
  | Unglue Tm ~Sys           -- unglue g [α ↦ B]

  | Hole Hole

  | Com I I Name Tm SysHCom Tm

  | WkI Tm

  -- builtins
  | Refl ~Tm
  | Sym ~Tm ~Tm ~Tm Tm
  | Trans ~Tm ~Tm ~Tm ~Tm Tm Tm
  | Ap Tm ~Tm ~Tm Tm
  deriving Show

data SrcHole
  = SHNamed Name
  | SHUnnamed
  | SHSilent
  deriving Show

data Hole
  = SrcHole SrcHole ~ParsedPos
  | ErrHole String
  deriving Show

data Cases
  = CSNil
  | CSCons Name [Name] Tm Cases
  deriving Show

data HCases
  = HCSNil
  | HCSCons Name [Name] [Name] Tm HCases
  deriving Show

data Sys = SEmpty | SCons Cof Tm Sys
  deriving Show

data SysHCom = SHEmpty | SHCons Cof Name Tm SysHCom
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

data Env
  = ENil
  | EDef Env ~Val

instance Show Env where
  show = show . go [] where
    go acc ENil         = acc
    go acc (EDef env v) = go (v:acc) env

type EnvArg = (?env :: Env)

--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------

data NeSys
  = NSEmpty
  | NSCons (BindCofLazy Val) NeSys
  deriving Show

data NeSysHCom
  = NSHEmpty
  | NSHCons (BindCof (BindILazy Val)) NeSysHCom
  deriving Show

isEmptyNSH :: NeSysHCom -> Bool
isEmptyNSH = \case NSHEmpty -> True; _ -> False
{-# inline isEmptyNSH #-}

data VSys
  = VSTotal Val
  | VSNe NeSys
  deriving Show

data VSysHCom
  = VSHTotal (BindILazy Val)
  | VSHNe NeSysHCom
  deriving Show

type VTy = Val

data Val
  = VSub Val Sub

  -- Delayed definition unfolding; the first value is the non-unfolded version,
  -- the second is the unfolded one. Unlike in MLTT, it's not easy to use neutrals
  -- to represent blocked unfoldings, because it is very much possible to compute
  -- away blocked unfoldings via cubical reductions.
  | VUnf {-# nounpack #-} DefInfo Frozen ~Val

  -- Neutrals. Not stable under substitution, no computation can ever match on them.
  | VNe Ne

  -- Semineutrals. Not stable under substitution but computation can match on them.

  -- NOTE: VHCom includes all stuck hcom-s, not just the HIT hcom-s.
  -- Only HIT hcom-s can be scrutinized in computation. The other hcom cases
  -- have to be handled in all other places as ordinary neutrals.

  | VGlueTy VTy NeSys                                        -- coe can act on it
  | VHDCon {-# nounpack #-} HDConInfo Env VDSpine Sub        -- case can act on it
  | VHCom I I VTy NeSysHCom Val                              -- coe and case can act on it
  | VGlue Val ~NeSys NeSys                                   -- unglue can act on it

  -- Canonicals. Stable under substitution.
  | VPi VTy NamedClosure
  | VLam NamedClosure
  | VPath NamedIClosure Val Val
  | VPLam ~Val ~Val NamedIClosure  -- annotated with endpoints
  | VSg VTy NamedClosure
  | VPair Name Val Val
  | VWrap Name VTy
  | VPack Name Val
  | VU
  | VLine NamedIClosure
  | VLLam NamedIClosure
  | VTyCon {-# nounpack #-} TyConInfo Env
  | VHTyCon {-# nounpack #-} HTyConInfo Env
  | VDCon {-# nounpack #-} DConInfo VDSpine

  -- misc
  | VHole Hole
  deriving Show

data Ne
  = NLocalVar Lvl
  | NDontRecurse {-# nounpack #-} RecInfo
  | NSub Ne Sub
  | NApp Ne Val
  | NPApp ~Val ~Val Ne I
  | NLApp Ne I
  | NProj1 Ne Name
  | NProj2 Ne Name
  | NUnpack Ne Name
  | NCoe I I (BindI Val) Val
  | NUnglue Ne NeSys
  | NCase Val NamedClosure (EvalClosure Cases)
  | NHCase Val NamedClosure (EvalClosure HCases)
  deriving Show

data Frozen
  = FTopVar {-# nounpack #-} DefInfo
  | FSub Frozen Sub
  | FApp Frozen ~Val
  | FPApp ~Val ~Val Frozen I
  | FLApp Frozen I
  | FProj1 Name Frozen
  | FProj2 Name Frozen
  | FUnpack Frozen Name
  | FCoeTy I I (BindI Frozen) ~Val
  | FCoeVal I I ~(BindI Val) Frozen
  | FHComTy I I Frozen NeSysHCom ~Val
  | FHComVal I I Val NeSysHCom Frozen
  | FUnglue Frozen NeSys
  | FCase_ Frozen NamedClosure (EvalClosure Cases)
  | FHCase_ Frozen NamedClosure (EvalClosure HCases)
  deriving Show

data VDSpine
  = VDNil
  | VDCons Val VDSpine
  deriving Show

--------------------------------------------------------------------------------

vVar :: Lvl -> Val
vVar x = VNe (NLocalVar x)
{-# inline vVar #-}

type DomArg  = (?dom  :: Lvl)    -- fresh LocalVar
type IDomArg = (?idom :: IVar)   -- fresh LocalVar

--------------------------------------------------------------------------------

data Recurse = Recurse ~(DontShow Val) | DontRecurse
  deriving Show

type RecurseArg = (?recurse :: Recurse)

data EvalClosure a = EC Sub Env Recurse a
  deriving Show

data EvalClosureLazy a = ECL Sub Env Recurse ~a
  deriving Show

-- | Defunctionalized closures.
data Closure
  -- ^ Body of vanilla term evaluation.
  = CEval (EvalClosure Tm)

  -- ^ Used for evaluating lazy terms coming from elaboration.
  | CEvalLazy (EvalClosureLazy Tm)

  -- ^ Body of lambdaCase
  | CSplit NamedClosure (EvalClosure Cases)
  | CHSplit NamedClosure (EvalClosure HCases) -- HIT version

  -- ^ Body of function coercions.
  | CCoePi I I (BindI VTy) (BindI NamedClosure) Val

  -- ^ Body of function hcom.
  | CHComPi I I VTy NamedClosure NeSysHCom Val

  | CConst Val
  -- | CConstLazy ~Val

  | C'λ'a''a        -- λ a. a
  | C'λ'a'i''a      -- λ a i. a
  | C'λ'a'i'j''a    -- λ a i j. a

{-
  coeIsEquiv : (A : I → U) (r r' : I) → isEquiv (λ x. coe r r' A x)
  coeIsEquiv A r r' =

    ffill i x      := coe r i A x
    gfill i x      := coe i r A x
    linvfill i x j := hcom r i (A r) [j=0 k. coe k r A (coe r k A x); j=1 k. x] x
    rinvfill i x j := hcom i r (A i) [j=0 k. coe k i A (coe i k A x); j=1 k. x] x

    g    := λ x^0. gfill r' x
    linv := λ x^0 j^1. linvfill r' x j
    rinv := λ x^0 j^1. rinvfill r' x j
    coh  := λ x^0 l^1 k^2. com r r' A [k=0 i. ffill i (linvfill i x l)
                                      ;k=1 i. ffill i x
                                      ;l=0 i. rinvfill i (ffill i x) k
                                      ;l=1 i. ffill i x]
                                      x
-}

  | CCoeAlong (BindI Val) I I -- λ x. coe a r r' x
  | CCoeLinv0 (BindI Val) I I -- a r r'
  | CCoeRinv0 (BindI Val) I I -- a r r'
  | CCoeCoh0 (BindI Val)  I I -- a r r'

-- isEquiv : (A → B) → U
-- isEquiv A B f :=
--     (g^1    : B → A)
--   × (linv^2 : (x^4 : A) → Path A (g (f x)) x)
--   × (rinv^3 : (x^5 : B) → Path B (f (g x)) x)
--   × (coh    : (x^6 : A) →
--             Path (i^7) (Path B (f (linv x {x}{g (f x)} i)) (f x))
--                   (refl B (f x))
--                   (rinv (f x)))

  | CIsEquiv1 Val Val Val         -- A B f
  | CIsEquiv2 Val Val Val Val     -- A B f g
  | CIsEquiv3 Val Val Val Val Val -- A B f g linv
  | CIsEquiv4 Val Val Val         -- A f g
  | CIsEquiv5 Val Val Val         -- B f g
  | CIsEquiv6 Val Val Val Val Val -- B f g linv rinv


  -- [A, B]  equiv A B = (f* : A -> B) × isEquiv A B f
  | CEquiv Val Val

  -- [A]  (B* : U) × equiv B A
  | CEquivInto Val

  deriving Show

-- | Defunctionalized closures for ivar abstraction
data IClosure
  = ICEval Sub Env Recurse Tm
  | ICCoePath I I (BindI NamedIClosure) (BindI Val) (BindI Val) Val
  | ICHComPath I I NamedIClosure Val Val NeSysHCom Val
  | ICConst Val
  | ICIsEquiv7 Val Val Val Val Val
  | ICHComLine I I NamedIClosure NeSysHCom Val
  | ICCoeLine I I (BindI NamedIClosure) Val

  | ICCoeLinv1 (BindI Val) I I Val -- a r r' x
  | ICCoeRinv1 (BindI Val) I I Val -- a r r' x

{-
  coeIsEquiv : (A : I → U) (r r' : I) → isEquiv (λ x. coe r r' A x)
  coeIsEquiv A r r' =

    ffill i x      := coe r i A x
    gfill i x      := coe i r A x
    linvfill i x j := hcom r i (A r) [j=0 k. coe k r A (coe r k A x); j=1 k. x] x
    rinvfill i x j := hcom i r (A i) [j=0 k. coe k i A (coe i k A x); j=1 k. x] x

    g    := λ x^0. gfill r' x
    linv := λ x^0 j^1. linvfill r' x j
    rinv := λ x^0 j^1. rinvfill r' x j
    coh  := λ x^0 l^1 k^2. com r r' A [k=0 i. ffill i (linvfill i x l)
                                      ;k=1 i. ffill i x
                                      ;l=0 i. rinvfill i (ffill i x) k
                                      ;l=1 i. ffill i x]
                                      x
-}

  | ICCoeCoh1 (BindI Val) I I Val    -- a r r' x
  | ICCoeCoh2 (BindI Val) I I Val I  -- a r r' x l
  | ICCoeCoh0Lhs (BindI Val) I I Val -- a r r' x

  | ICSym Val ~Val ~Val Val
  | ICTrans Val ~Val ~Val ~Val Val Val
  | ICAp Val ~Val ~Val Val

  | ICBindI (BindI Val)
  deriving Show

--------------------------------------------------------------------------------

rebind :: BindI a -> b -> BindI b
rebind (BindI x i _) b = BindI x i b
{-# inline rebind #-}

rebindLazy :: BindILazy a -> b -> BindILazy b
rebindLazy (BindILazy x i _) b = BindILazy x i b
{-# inline rebindLazy #-}

-- Substitution
----------------------------------------------------------------------------------------------------

instance SubAction NeCof where
  sub = \case
    NCEq i j    -> NCEq (sub i) (sub j)

instance SubAction a => SubAction (BindCofLazy a) where
  sub (BindCofLazy cof a) = BindCofLazy (sub cof) (sub a); {-# inline sub #-}

instance SubAction a => SubAction (BindCof a) where
  sub (BindCof cof a) = BindCof (sub cof) (sub a); {-# inline sub #-}

instance SubAction Val where
  sub = \case
    VSub v s' -> VSub v (sub s')
    v         -> VSub v ?sub
  {-# inline sub #-}

instance SubAction Ne where
  sub = \case
    NSub n s' -> NSub n (sub s')
    n         -> NSub n ?sub
  {-# inline sub #-}

instance SubAction Frozen where
  sub t = FSub t ?sub
  {-# inline sub #-}

instance SubAction NeSys where
  sub = \case
    NSEmpty      -> NSEmpty
    NSCons t sys -> NSCons (sub t) (sub sys)

instance SubAction NeSysHCom where
  sub = \case
    NSHEmpty      -> NSHEmpty
    NSHCons t sys -> NSHCons (sub t) (sub sys)

instance SubAction Env where
  sub e = case e of
    ENil     -> ENil
    EDef e v -> EDef (sub e) (sub v)

instance SubAction a => SubAction (BindI a) where
  sub (BindI x i a) =
    let fresh = dom ?sub in
    let ?sub  = lift (setCod i ?sub) in
    seq ?sub (BindI x fresh (sub a))
  {-# inline sub #-}

instance SubAction a => SubAction (BindILazy a) where
  sub (BindILazy x i a) =
    let fresh = dom ?sub in
    let ?sub  = lift (setCod i ?sub) in
    seq ?sub (BindILazy x fresh (sub a))
  {-# inline sub #-}

instance SubAction a => SubAction (DontShow a) where
  sub (DontShow a) = DontShow (sub a)

instance SubAction NamedClosure where
  sub (NCl x cl) = NCl x (sub cl)
  {-# inline sub #-}

instance SubAction NamedIClosure where
  sub (NICl x cl) = NICl x (sub cl)
  {-# inline sub #-}

instance SubAction (EvalClosure a) where
  sub (EC s' env rc t) = EC (sub s') (sub env) rc t
  {-# inline sub #-}

instance SubAction (EvalClosureLazy a) where
  sub (ECL s' env rc t) = ECL (sub s') (sub env) rc t
  {-# inline sub #-}

instance SubAction Closure where
  sub cl = case cl of
    CEval     ecl -> CEval (sub ecl)
    CEvalLazy ecl -> CEvalLazy (sub ecl)
    CSplit  b ecl -> CSplit (sub b) (sub ecl)
    CHSplit b ecl -> CHSplit (sub b) (sub ecl)

    -- note: recursive closure sub below! This is probably
    -- fine, because recursive depth is bounded by Pi type nesting.
    CCoePi r r' a b t ->
      CCoePi (sub r) (sub r') (sub a) (sub b) (sub t)

    CHComPi r r' a b sys base ->
      CHComPi (sub r) (sub r') (sub a) (sub b) (sub sys) (sub base)

    CConst t                  -> CConst (sub t)
    -- CConstLazy t              -> CConstLazy (sub t)
    CIsEquiv1 a b f           -> CIsEquiv1 (sub a) (sub b) (sub f)
    CIsEquiv2 a b f g         -> CIsEquiv2 (sub a) (sub b) (sub f) (sub g)
    CIsEquiv3 a b f g linv    -> CIsEquiv3 (sub a) (sub b) (sub f) (sub g) (sub linv)
    CIsEquiv4 a f g           -> CIsEquiv4 (sub a) (sub f) (sub g)
    CIsEquiv5 b f g           -> CIsEquiv5 (sub b) (sub f) (sub g)
    CIsEquiv6 b f g linv rinv -> CIsEquiv6 (sub b) (sub f) (sub g) (sub linv) (sub rinv)
    CEquiv a b                -> CEquiv (sub a) (sub b)
    CEquivInto a              -> CEquivInto (sub a)
    C'λ'a''a                  -> C'λ'a''a
    C'λ'a'i''a                -> C'λ'a'i''a
    C'λ'a'i'j''a              -> C'λ'a'i'j''a
    CCoeAlong a r r'          -> CCoeAlong (sub a) (sub r) (sub r')
    CCoeLinv0 a r r'          -> CCoeLinv0 (sub a) (sub r) (sub r')
    CCoeRinv0 a r r'          -> CCoeRinv0 (sub a) (sub r) (sub r')
    CCoeCoh0 a r r'           -> CCoeCoh0 (sub a) (sub r) (sub r')

instance SubAction IClosure where
  sub cl = case cl of
    ICEval s' env rc t ->
      ICEval (sub s') (sub env) rc t

    -- recursive sub here as well!
    ICCoePath r r' a lh rh p ->
      ICCoePath (sub r) (sub r') (sub a) (sub lh) (sub rh) (sub p)

    ICHComPath r r' a lhs rhs sys base ->
      ICHComPath (sub r) (sub r') (sub a) (sub lhs) (sub rhs) (sub sys) (sub base)

    ICConst t               -> ICConst (sub t)
    ICIsEquiv7 b f g linv x -> ICIsEquiv7 (sub b) (sub f) (sub g) (sub linv) (sub x)
    ICHComLine r r' a t b   -> ICHComLine (sub r) (sub r') (sub a) (sub t) (sub b)
    ICCoeLine r r' a t      -> ICCoeLine (sub r) (sub r') (sub a) (sub t)
    ICCoeLinv1 a x r r'     -> ICCoeLinv1 (sub a) (sub x) (sub r) (sub r')
    ICCoeRinv1 a x r r'     -> ICCoeRinv1 (sub a) (sub x) (sub r) (sub r')
    ICSym a x y p           -> ICSym (sub a) (sub x) (sub y) (sub p)
    ICTrans a x y z p q     -> ICTrans (sub a) (sub x) (sub y) (sub z) (sub p) (sub q)
    ICAp f x y p            -> ICAp (sub f) (sub x) (sub y) (sub p)
    ICCoeCoh1 a r r' x      -> ICCoeCoh1 (sub a) (sub r) (sub r') (sub x)
    ICCoeCoh2 a r r' x l    -> ICCoeCoh2 (sub a) (sub r) (sub r') (sub x) (sub l)
    ICCoeCoh0Lhs a r r' x   -> ICCoeCoh0Lhs (sub a) (sub r) (sub r') (sub x)
    ICBindI a               -> ICBindI (sub a)

instance SubAction VDSpine where
  sub = \case
    VDNil       -> VDNil
    VDCons v vs -> VDCons (sub v) (sub vs)


-- Semantics functions indicate in result whether they made progress This is
-- needed in forcing where we need to stop recursing when no progress was made.
--------------------------------------------------------------------------------

data Res = Res {resVal :: Val, resProgressed :: Bool}
  deriving Show

block :: Val -> Res
block v = Res v False
{-# inline block #-}

progress :: Val -> Res
progress v = Res v True
{-# inline progress #-}

--------------------------------------------------------------------------------

makeFields ''BindCof
makeFields ''BindCofLazy
makeFields ''BindI
makeFields ''BindILazy
makeFields ''DConInfo
makeFields ''DefInfo
makeFields ''HDConInfo
makeFields ''HTyConInfo
makeFields ''NamedClosure
makeFields ''NamedIClosure
makeFields ''RecInfo
makeFields ''TyConInfo
makeFields ''Res
