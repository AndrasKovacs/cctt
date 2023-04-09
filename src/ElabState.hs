
module ElabState where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.IORef
import Data.Time.Clock

import Common
import CoreTypes
import Interval
import qualified LvlMap as LM

type Constructors = LM.Map (Name, [(Name, Ty)])

data TblEntry
  = TBETopDef Lvl VTy ~Val SourcePos   -- level, type, value
  | TBETyCon Lvl [(Name, Ty)] Constructors SourcePos
  | TBEDCon Lvl Lvl [(Name, Ty)] SourcePos
  | TBELocal Lvl VTy                   -- level, type
  | TBELocalInt IVar
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
  | TPETyCon [(Name, Ty)] Constructors IsCaseAllowed
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
makeFields ''TopState

initialTop :: TopState
initialTop = TopState mempty 0 mempty mempty mempty Nothing "" "" False False 0

topState :: IORef TopState
topState = runIO $ newIORef initialTop
{-# noinline topState #-}

indTypeInfo :: Lvl -> IO ([(Name, Ty)], Constructors, Bool)
indTypeInfo typeid = do
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

modIndTypeInfo ::
       Lvl
    -> (([(Name, Ty)], Constructors, Bool) -> ([(Name, Ty)], Constructors, Bool))
    -> IO ()
modIndTypeInfo tyid f = do
  modTop $
    topInfo %~ flip LM.adjust tyid
      \case TPETyCon ps cs canCase -> case f (ps, cs, canCase) of
              (!ps, !cs, !canCase) -> TPETyCon ps cs canCase
            _ -> impossible
{-# inline modIndTypeInfo #-}

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

defineTop :: Name -> VTy -> Val -> SourcePos -> IO ()
defineTop x ~a ~v pos =
  modTop \top ->
     top & lvl     +~ 1
         & tbl     %~ M.insert x (TBETopDef (top^.lvl) a v pos)
         & topInfo %~ LM.insert (top^.lvl) (TPEDef a v)

-- | Declare a TyCon without constructors. This happens before the constructors are
--   elaborated.
declareNewTyCon :: Name -> [(Name, Ty)] -> SourcePos -> IO Lvl
declareNewTyCon x ps pos = do
  top <- getTop
  let tyid = top^.lvl
  putTop $
    top & lvl     +~ 1
        & tbl     %~ M.insert x (TBETyCon tyid ps mempty pos)
        & topInfo %~ LM.insert tyid (TPETyCon ps mempty False)
  pure tyid

-- | Set the TyCon as case-able.
finalizeTyCon :: Lvl -> IO ()
finalizeTyCon tyid = do
  modIndTypeInfo tyid \(ps, cs, canCase) -> (ps, cs, True)

-- | Extend a TyCon with an extra constructor.
addDCon :: Name -> Lvl -> Lvl -> [(Name, Ty)] -> SourcePos -> IO ()
addDCon x tyid conid fields pos =
  modIndTypeInfo tyid \(ps, cs, canCase) ->
    (ps, LM.insert conid (x, fields) cs, canCase)

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
