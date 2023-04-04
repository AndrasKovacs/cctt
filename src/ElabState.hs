
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
  = TBETop Lvl VTy ~Val SourcePos   -- level, type, value
  | TBELocal Lvl VTy                -- level, type
  | TBELocalInt IVar
  | TBETyCon Lvl [(Name, Ty)] [(Name, [(Name, Ty)])]
  | TBEDCon Lvl Lvl [(Name, Ty)]
  deriving Show

data Box a = Box ~a deriving (Show)

type Table      = M.Map Name TblEntry
type TableArg   = (?tbl        :: Table)
type PosArg     = (?srcPos     :: SourcePos)
type TopLvl     = (?topLvl     :: Lvl)
type LocalTypes = (?localTypes :: [Box VTy])

data TopEntry
  = TPEDef VTy ~Val
  | TPEInductive [(Name, Ty)] [(Name, [(Name, Ty)])]
  deriving Show

data TopState = TopState {
    topStateTopInfo      :: LM.LvlMap TopEntry
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

indTypeInfo :: Elab (Lvl -> IO ([(Name, Ty)], [(Name, [(Name, Ty)])]))
indTypeInfo typeid = do
  top <- getTop
  case LM.lookup typeid (top^.topInfo) of
    Just (TPEInductive paramtypes contypes) -> pure (paramtypes, contypes)
    _                                       -> impossible

modTop :: (TopState -> TopState) -> IO ()
modTop = modifyIORef' topState

getTop :: IO TopState
getTop = readIORef topState

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
