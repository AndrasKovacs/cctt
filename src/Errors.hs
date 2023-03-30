
module Errors where

import Control.Exception
import qualified Data.Map.Strict as M
import Data.List

import Common
import CoreTypes
import ElabState
import Interval
import Pretty

data Error
  = NameNotInScope Name
  | LocalLvlNotInScope
  | TopLvlNotInScope
  | UnexpectedI
  | UnexpectedIType
  | ExpectedI
  | ExpectedPiPathLine Tm
  | ExpectedSg Tm
  | ExpectedGlueTy Tm
  | ExpectedPathLine Tm
  | ExpectedPath Tm
  | ExpectedPathULineU Tm
  | ExpectedNonDepFun Tm
  | CantInferLam
  | CantInferPair
  | CantInfer
  | CantInferGlueTm
  | CantConvert Tm Tm
  | CantConvertCof Cof Cof
  | CantConvertEndpoints Tm Tm
  | CantConvertReflEndpoints Tm Tm
  | CantConvertExInf Tm Tm
  | GlueTmSystemMismatch Sys
  | TopShadowing SourcePos
  | NonNeutralCofInSystem
  | NoSuchField Tm
  | CantInferHole
  | ImportCycle FilePath [FilePath]
  | CantOpenFile FilePath
  deriving Show

instance Exception Error where

data ErrInCxt where
  ErrInCxt :: (TableArg, PosArg, NCofArg, DomArg) => Error -> ErrInCxt

instance Show ErrInCxt where
  show (ErrInCxt e) = show e

instance Exception ErrInCxt

err :: TableArg => PosArg => NCofArg => DomArg => Error -> IO a
err e = throwIO $ ErrInCxt e

-- | Convert the symbol table to a printing environment.
withPrettyArgs :: TableArg => DomArg => NCofArg => PrettyArgs a -> a
withPrettyArgs act =
  let entryToNameKey = \case
        Top x _ _ _  -> NKTop x
        Local x _    -> NKLocal x
        LocalInt x   -> NKLocalI x in
  let ?idom   = dom ?cof
      ?names  = M.foldlWithKey'
                  (\acc name e -> M.insert (entryToNameKey e) name acc)
                  mempty ?tbl
      ?shadow = mempty in
  act
{-# inline withPrettyArgs #-}

showError :: PrettyArgs (Error -> String)
showError = \case
  CantConvertExInf t u ->
    "Can't convert expected type\n\n" ++
    "  " ++ pretty u ++ "\n\n" ++
    "and inferred type\n\n" ++
    "  " ++ pretty t

  CantInfer ->
    "Can't infer type for expression"

  CantConvert t u ->
    "Can't convert\n\n" ++
    "  " ++ pretty u ++ "\n\n" ++
    "and\n\n" ++
    "  " ++ pretty t

  CantConvertEndpoints t u ->
    "Can't convert expected path endpoint\n\n" ++
    "  " ++ pretty u ++ "\n\n" ++
    "to the inferred endpoint\n\n" ++
    "  " ++ pretty t

  CantConvertReflEndpoints t u ->
    "Can't convert endpoints when checking \"refl\":\n\n" ++
    "  " ++ pretty u ++ "\n\n" ++
    "  " ++ pretty t

  CantConvertCof c1 c2 ->
    "Can't convert expected path endpoint\n\n" ++
    "  " ++ pretty c1 ++ "\n\n" ++
    "to\n\n" ++
    "  " ++ pretty c2

  NameNotInScope x ->
    "Name not in scope: " ++ x

  LocalLvlNotInScope ->
    "Local De Bruijn level not in scope"

  TopLvlNotInScope ->
    "Top-level De Bruijn level not in scope"

  TopShadowing pos ->
       "Duplicate top-level name.\n"
    ++ "Previously defined at: " ++ sourcePosPretty pos

  UnexpectedI ->
    "Unexpected interval expression"

  ExpectedI ->
    "Expected an interval expression"

  ExpectedPath a ->
    "Expected a path type, inferred\n\n" ++
    "  " ++ pretty a

  ExpectedPiPathLine a ->
    "Expected a function, line or path type, inferred\n\n" ++
    "  " ++ pretty a

  ExpectedSg a ->
    "Expected a sigma type, inferred\n\n" ++
    "  " ++ pretty a

  ExpectedGlueTy a ->
    "Expected a glue type, inferred\n\n" ++
    "  " ++ pretty a

  ExpectedPathLine a ->
    "Expected a path type or a line type, inferred\n\n" ++
    "  " ++ pretty a

  ExpectedPathULineU a ->
    "Expected a path type or a line type in U, inferred\n\n" ++
    "  " ++ pretty a

  ExpectedNonDepFun a ->
    "Expected a non-dependent function type, inferred\n\n" ++
    "  " ++ pretty a

  CantInferLam ->
    "Can't infer type for lambda expression"

  CantInferPair ->
    "Can't infer type for pair expression"

  CantInferGlueTm ->
    "Can't infer type for glue expression"

  GlueTmSystemMismatch sys ->
    "Can't match glue system with expected Glue type system\n\n" ++
    "  " ++ pretty sys

  UnexpectedIType ->
    "The type of intervals I can be only used in function domains"

  NonNeutralCofInSystem ->
    "Only neutral cofibrations are allowed in systems"

  NoSuchField a ->
    "Field projection is not supported by inferred type:\n\n" ++
    "  " ++ pretty a

  CantInferHole ->
    "Can't infer type for hole"

  ImportCycle path cycle ->
    "Imports form a cycle:\n\n"
    ++ intercalate " -> " (dropWhile (/=path) cycle ++ [path])

  CantOpenFile path ->
    "Can't open file: " ++ path

displayErrInCxt :: ErrInCxt -> IO ()
displayErrInCxt (ErrInCxt e) = withPrettyArgs do
  file <- getTop <&> (^.currentSrc)
  modTop (errPrinting .~ True)

  let SourcePos path (unPos -> linum) (unPos -> colnum) = ?srcPos
      lnum = show linum
      lpad = map (const ' ') lnum

  putStrLn ("\nERROR " ++ path ++ ":" ++ lnum ++ ":" ++ show colnum)
  putStrLn (lpad ++ " |")
  putStrLn (lnum ++ " | " ++ (lines file !! (linum - 1)))
  putStrLn (lpad ++ " | " ++ replicate (colnum - 1) ' ' ++ "^")
  putStrLn (showError e)
  putStrLn ""
