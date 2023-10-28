
module ElabState where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.IORef
import Data.Time.Clock

import Common
import CoreTypes
import Cubical

import qualified Presyntax as P
import qualified Data.LvlMap as LM
import qualified Data.ByteString.Char8 as B

data TopEntry
  = TEDef DefInfo
  | TERec (Maybe RecInfo)
  | TETyCon TyConInfo
  | TEDCon DConInfo
  | TEHTyCon HTyConInfo
  | TEHDCon HDConInfo
  deriving Show

data Locals
  = LNil
  | LBind  Locals Name ~VTy ~Ty
  | LBindI Locals Name
  | LCof   Locals NeCof
  deriving Show

data RevLocals
  = RLNil
  | RLBind Name ~VTy ~Ty RevLocals
  | RLBindI Name RevLocals
  | RLCof NeCof RevLocals
  deriving Show

revLocals :: Locals -> RevLocals
revLocals = go RLNil where
  go acc LNil              = acc
  go acc (LBind ls x a qa) = go (RLBind x a qa acc) ls
  go acc (LBindI ls r)     = go (RLBindI r acc) ls
  go acc (LCof ls c)       = go (RLCof c acc) ls

lookupLocalType :: Ix -> Locals -> Box VTy
lookupLocalType x ls = case (x, ls) of
  (0, LBind _ _ a _ ) -> Box a
  (x, LBind ls _ _ _) -> lookupLocalType (x - 1) ls
  (x, LBindI ls _   ) -> lookupLocalType x ls
  (x, LCof ls _     ) -> lookupLocalType x ls
  _                   -> impossible

type PosArg     = (?srcPos  :: Box Pos)
type LocalsArg  = (?locals  :: Locals)
type Elab a     = LocalsArg => NCofArg => DomArg => EnvArg => PosArg => a

data PrintingOpts = PrintingOpts {
    printingOptsVerbose            :: Bool
  , printingOptsErrPrinting        :: Bool
  , printingOptsPrintNextUnfolding :: Bool
  , printingOptsShowHoleCxts       :: Bool }
  deriving Show

data LoadState = LoadState {
    loadStateLoadedFiles :: S.Set FilePath
  , loadStateCurrentPath :: FilePath        -- path of file being currently processed

  , loadStateBasePath    :: FilePath        -- Base path of the module hierarchy.

  , loadStateLoadCycle   :: [FilePath]      -- Chain of imports going back to original input file to cctt.
                                            -- We check for import cycles on this.
  , loadStateCurrentSrc  :: B.ByteString
  } deriving Show

data HCaseBoundaryCheck where
  HCBC :: (LocalsArg, NCofArg, DomArg, EnvArg, PosArg) =>
    Env -> [HDConInfo] -> NamedClosure -> HCases -> HCaseBoundaryCheck
  deriving Show via DontShow HCaseBoundaryCheck

data State = State {
    stateTop                 :: M.Map B.ByteString TopEntry
  , stateTop'                :: LM.Map TopEntry
  , stateLvl                 :: Lvl
  , stateLoadState           :: LoadState
  , stateParsingTime         :: NominalDiffTime
  , statePrintingOpts        :: PrintingOpts
  , stateHCaseBoundaryChecks :: [HCaseBoundaryCheck]
  , stateUnfolding           :: Bool
  } deriving Show

makeFields ''LoadState
makeFields ''State
makeFields ''PrintingOpts

defaultPrintingOpts :: PrintingOpts
defaultPrintingOpts = PrintingOpts False False False True

initLoadState :: LoadState
initLoadState = LoadState mempty mempty mempty mempty mempty

initState :: State
initState = State mempty mempty 0 initLoadState 0 defaultPrintingOpts [] False

stateRef :: IORef State
stateRef = runIO $ newIORef initState
{-# noinline stateRef #-}

getState :: IO State
getState = readIORef stateRef

putState :: State -> IO ()
putState = writeIORef stateRef

modState :: (State -> State) -> IO ()
modState = modifyIORef' stateRef

resetElabState :: IO ()
resetElabState = putState initState

withTopElab :: Elab (IO a) -> IO a
withTopElab act = do
  st <- getState
  let ls = st^.loadState
  let ?locals = LNil
      ?cof    = emptyNCof
      ?dom    = 0
      ?env    = ENil
      ?srcPos = Box $! initialPos (SrcFile (ls^.currentPath) (ls^.currentSrc))
  act
{-# inline withTopElab #-}

-- | Bind a fibrant variable.
bind :: Name -> VTy -> Ty -> Elab (Val -> a) -> Elab a
bind x ~a ~qa act =
  let v       = vVar ?dom in
  let ?dom    = ?dom + 1
      ?env    = EDef ?env v
      ?locals = LBind ?locals x a qa in
  let _ = ?dom; _ = ?env in
  act v
{-# inline bind #-}

-- | Define a fibrant variable.
define :: Name -> VTy -> Ty -> Val -> Elab a -> Elab a
define x ~a ~qa ~v act =
  let ?env    = EDef ?env v
      ?dom    = ?dom + 1
      ?locals = LBind ?locals x a qa in
  let _ = ?env; _ = ?dom in
  act
{-# inline define #-}

bindToName :: P.Bind -> Name
bindToName = \case
  P.BName x     -> NSpan x
  P.BDontBind _ -> N_

-- | Bind an ivar.
bindI :: Name -> Elab (IVar -> a) -> Elab a
bindI x act =
  let fresh = dom ?cof in
  if  fresh == maxIVar then error "RAN OUT OF IVARS IN ELABORATION" else
  let ?cof    = lift ?cof in
  let ?locals = LBindI ?locals x in
  seq ?cof $ act fresh
{-# inline bindI #-}

bindCof :: NeCof' -> Elab a -> Elab a
bindCof (NeCof' cof c) act =
  let ?cof    = cof
      ?locals = LCof ?locals c in
  act; {-# inline bindCof #-}

isNameUsed :: Elab (B.ByteString -> Bool)
isNameUsed x = go ?locals x where
  go :: Locals -> B.ByteString -> Bool
  go LNil              _ = False
  go (LBind ls x' _ _) x = x == nameToBs x' || go ls x
  go (LBindI ls x')    x = x == nameToBs x' || go ls x
  go (LCof ls _)       x = go ls x

-- | Try to pick an informative fresh ivar name.
pickIVarName :: Elab Name
pickIVarName
  | not (isNameUsed "i") = i_
  | not (isNameUsed "j") = j_
  | not (isNameUsed "k") = k_
  | not (isNameUsed "l") = l_
  | not (isNameUsed "m") = m_
  | True                 = i_
