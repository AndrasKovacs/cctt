
module ElabState where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.IORef
import Data.Time.Clock

import Common
import CoreTypes
import Interval
import qualified LvlMap as LM

data TblEntry
  = TBETopDef Lvl VTy ~Val (DontShow SourcePos)   -- level, type, value
  | TBETyCon Lvl Tel Constructors (DontShow SourcePos)
  | TBEDCon Lvl Lvl Tel (DontShow SourcePos)
  | TBELocal Lvl VTy                   -- level, type
  | TBELocalInt IVar
  | TBETopRec Lvl (Maybe VTy) (DontShow SourcePos)
  deriving Show

data Box a = Box ~a deriving (Show)

type Table      = M.Map Name TblEntry
type TableArg   = (?tbl        :: Table)
type PosArg     = (?srcPos     :: SourcePos)
type TopLvl     = (?topLvl     :: Lvl)
type LocalTypes = (?localTypes :: [Box VTy])

-- | Case expressions are not allowed on a TyCon whose constructors are being defined.
type IsCaseAllowed = Bool

data TopEntry
  = TPEDef VTy ~Val
  | TPETyCon Tel Constructors IsCaseAllowed
  | TPERec (Maybe VTy)
  deriving Show

data TopState = TopState {
    topStateTopInfo      :: LM.Map TopEntry
  , topStateLvl          :: Lvl
  , topStateTbl          :: Table
  , topStateLoadedFiles  :: S.Set FilePath
  , topStateLoadCycle    :: [FilePath]
  , topStatePrintNf      :: Maybe Name
  , topStateCurrentPath  :: FilePath
  , topStateCurrentSrc   :: String
  , topStateVerbose      :: Bool
  , topStateErrPrinting  :: Bool
  , topStateParsingTime  :: NominalDiffTime}
  deriving Show
makeFields ''TopState

initialTop :: TopState
initialTop = TopState mempty 0 mempty mempty mempty Nothing "" "" False False 0

topState :: IORef TopState
topState = runIO $ newIORef initialTop
{-# noinline topState #-}

tyConInfo :: Lvl -> IO (Tel, Constructors, Bool)
tyConInfo typeid = do
  top <- getTop
  case LM.lookup typeid (top^.topInfo) of
    Just (TPETyCon paramtypes contypes canCase) -> pure (paramtypes, contypes, canCase)
    _ -> impossible

modTop :: (TopState -> TopState) -> IO ()
modTop = modifyIORef' topState

getTop :: IO TopState
getTop = readIORef topState

putTop :: TopState -> IO ()
putTop = writeIORef topState

modTyConInfo ::
       Lvl
    -> ((Tel, Constructors, Bool) -> (Tel, Constructors, Bool))
    -> IO ()
modTyConInfo tyid f = do
  modTop $
    topInfo %~ flip LM.adjust tyid
      \case TPETyCon ps cs canCase -> case f (ps, cs, canCase) of
              (!ps, !cs, !canCase) -> TPETyCon ps cs canCase
            _ -> impossible
{-# inline modTyConInfo #-}

type Elab a = LocalTypes => NCofArg => DomArg => EnvArg => TableArg => PosArg => a

resetTop :: IO ()
resetTop = modTop \_ -> initialTop

withTopElab :: Elab (IO a) -> IO a
withTopElab act = do
  top <- getTop
  let ?tbl        = top^.tbl
      ?cof        = idSub 0
      ?dom        = 0
      ?env        = ENil
      ?srcPos     = initialPos (top^.currentPath)
      ?localTypes = []
  act
{-# inline withTopElab #-}

declareTopDef :: Name -> Maybe VTy -> DontShow SourcePos -> (TableArg => Lvl -> IO a) -> TableArg => IO a
declareTopDef x a pos act = do
  top <- getTop
  let l    = top^.lvl
  let tbl' = M.insert x (TBETopRec l a pos) (top^.tbl)
  putTop $
    top & lvl     .~ l + 1
        & tbl     .~ tbl'
        & topInfo %~ LM.insert l (TPERec a)
  let ?tbl = tbl'
  act l
{-# inline declareTopDef #-}

-- | Convert a declared topdef to a type-annotated one.
finalizeTopDef :: Lvl -> Name -> VTy -> Val -> DontShow SourcePos -> IO ()
finalizeTopDef l x ~a ~v pos =
  modTop \top ->
     top & tbl     %~ M.insert x (TBETopDef l a v pos)
         & topInfo %~ LM.insert l (TPEDef a v)

-- | Declare a TyCon without constructors. This happens before the constructors are
--   elaborated.
declareNewTyCon ::
  Name -> Tel -> DontShow SourcePos -> (TableArg => Lvl -> IO a) -> (TableArg => IO a)
declareNewTyCon x ps pos act = do
  top <- getTop
  let tyid = top^.lvl
  let tbl' = M.insert x (TBETyCon tyid ps mempty pos) (top^.tbl)
  putTop $
    top & lvl     +~ 1
        & tbl     .~ tbl'
        & topInfo %~ LM.insert tyid (TPETyCon ps mempty False)
  let ?tbl = tbl'
  act tyid
{-# inline declareNewTyCon #-}

-- | Set the TyCon as case-able.
finalizeTyCon :: Lvl -> IO ()
finalizeTyCon tyid = do
  modTyConInfo tyid \(ps, cs, canCase) -> (ps, cs, True)

-- | Extend a TyCon with an extra constructor.
addDCon :: Name -> Lvl -> Lvl -> Tel -> DontShow SourcePos -> (TableArg => IO a) -> TableArg => IO a
addDCon x tyid conid fields pos act = do
  -- extend topcxt
  modTyConInfo tyid \(ps, cs, canCase) -> (ps, LM.insert conid (x, fields) cs, canCase)
  modTop (tbl %~ M.insert x (TBEDCon tyid conid fields pos))

  -- but independently, extend local cxt, because this one contains the type params as well,
  -- while the topcxt does not!
  let ?tbl = M.insert x (TBEDCon tyid conid fields pos) ?tbl
  act
{-# inline addDCon #-}

-- | Bind a fibrant variable.
bind :: Name -> VTy -> Elab (Val -> a) -> Elab a
bind x ~a act =
  let v           = vVar ?dom in
  let ?dom        = ?dom + 1
      ?env        = EDef ?env v
      ?tbl        = M.insert x (TBELocal ?dom a) ?tbl
      ?localTypes = Box a : ?localTypes in
  let _ = ?dom; _ = ?env; _ = ?tbl in
  act v
{-# inline bind #-}

-- | Define a fibrant variable.
define :: Name -> VTy -> Val -> Elab a -> Elab a
define x ~a ~v act =
  let ?env        = EDef ?env v
      ?dom        = ?dom + 1
      ?tbl        = M.insert x (TBELocal ?dom a) ?tbl
      ?localTypes = Box a : ?localTypes in
  let _ = ?env; _ = ?tbl; _ = ?dom in
  act
{-# inline define #-}

-- | Bind an ivar.
bindI :: Name -> Elab (IVar -> a) -> Elab a
bindI x act =
  let fresh = dom ?cof in
  let ?cof  = setDom (fresh + 1) ?cof `ext` IVar fresh
      ?tbl  = M.insert x (TBELocalInt fresh) ?tbl in
  let _ = ?cof; _ = ?tbl in
  act fresh
{-# inline bindI #-}

bindCof :: NeCof' -> Elab a -> Elab a
bindCof (NeCof' cof c) act = let ?cof = cof in act; {-# inline bindCof #-}

-- | Try to pick an informative fresh ivar name.
pickIVarName :: Elab Name
pickIVarName
  | M.notMember "i" ?tbl = "i"
  | M.notMember "j" ?tbl = "j"
  | M.notMember "k" ?tbl = "k"
  | M.notMember "l" ?tbl = "l"
  | M.notMember "m" ?tbl = "m"
  | True                 = "i"
