
module Errors where

import Control.Exception
import Data.List

import Common
import CoreTypes
import ElabState
import Cubical
import Pretty

data Error
  = NameNotInScope Name
  | LocalLvlNotInScope
  | TopLvlNotInScope
  | UnexpectedI
  | UnexpectedIType
  | ExpectedI
  | ExpectedPiPathLine ~Tm
  | ExpectedSg ~Tm
  | ExpectedGlueTy ~Tm
  | ExpectedPathLine ~Tm
  | ExpectedPath ~Tm
  | ExpectedPathULineU ~Tm
  | ExpectedNonDepFun ~Tm
  | CantInferLam
  | CantInferPair
  | CantInfer
  | CantInferGlueTm
  | CantConvert ~Tm ~Tm
  | CantConvertCof Cof Cof
  | CantConvertEndpoints ~Tm ~Tm
  | CantConvertReflEndpoints ~Tm ~Tm
  | CantConvertExInf ~Tm ~Tm
  | GlueTmSystemMismatch Sys
  | TopShadowing SourcePos
  | NonNeutralCofInSystem
  | NoSuchField Name ~Tm
  | CantInferHole
  | ImportCycle FilePath [FilePath]
  | CantOpenFile FilePath
  | GenericError String
  | ExpectedInductiveType ~Tm
  | CaseMismatch
  deriving Show

instance Exception Error where

data ErrInCxt where
  ErrInCxt :: (LocalsArg, NCofArg, DomArg, EnvArg, PosArg) => Error -> ErrInCxt

instance Show ErrInCxt where
  show (ErrInCxt e) = show e

instance Exception ErrInCxt

err :: Elab (Error -> IO a)
err e = throwIO $ ErrInCxt e

showError :: PrettyArgs (Error -> String)
showError = \case
  CaseMismatch ->
    "Case expressions must cover all constructors of an inductive type in the order of declaration"

  GenericError msg ->
    msg

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
       "Duplicate top-level name\n"
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

  NoSuchField x a ->
    "Field projection " ++ show x ++ " is not supported by inferred type:\n\n" ++
    "  " ++ pretty a

  CantInferHole ->
    "Can't infer type for hole"

  ImportCycle path cycle ->
    "Imports form a cycle:\n\n"
    ++ intercalate " -> " (dropWhile (/=path) cycle ++ [path])

  CantOpenFile path ->
    "Can't open file: " ++ path

  ExpectedInductiveType a ->
    "Expected an inductive type, inferred\n\n" ++
    "  " ++ pretty a

displayErrInCxt :: ErrInCxt -> IO ()
displayErrInCxt (ErrInCxt e) = withPrettyArgs do
  file <- getState <&> (^.loadState.currentSrc)
  modState (printingOpts.errPrinting .~ True)

  let SourcePos path (unPos -> linum) (unPos -> colnum) = ?srcPos
      lnum = show linum
      lpad = map (const ' ') lnum

  putStrLn ("\nERROR " ++ path ++ ":" ++ lnum ++ ":" ++ show colnum)
  putStrLn (lpad ++ " |")
  putStrLn (lnum ++ " | " ++ (lines file !! (linum - 1)))
  putStrLn (lpad ++ " | " ++ replicate (colnum - 1) ' ' ++ "^")
  putStrLn (showError e)
  putStrLn ""
