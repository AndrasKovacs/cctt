
module MainInteraction where

import qualified Data.Map.Strict as M
import System.Environment
import System.Exit
import qualified FlatParse.Stateful as FP
import Text.Read (readMaybe)
import Data.Maybe

import Common
import CoreTypes
import Core
import Cubical
import ElabState
import Elaboration
import Pretty
import Quotation
import Statistics

helpMsg = unlines [
   "usage: cctt <file> [nf <topdef>] [trace <topdef>] [trace-to-end <topdef>] [ty <topdef>] [elab] [verbose] [unfold] [no-hole-cxts]"
  ,""
  ,"Checks <file>. Options:"
  ,"  nf <topdef>           Prints the normal form of top-level definition <topdef>."
  ,"                        Implies the \"unfold\" option."
  ,"  trace <topdef>        Interactively steps through head unfoldings of a value."
  ,"  ty <topdef>           Prints the type of the top-level definition <topdef>."
  ,"  elab                  Prints the elaboration output."
  ,"  verbose               Prints path endpoints, hcom types and hole source positions explicitly."
  ,"                        Verbose output can be always re-checked by cctt."
  ,"  unfold                Option to immediately unfold all top definitions during evaluation."
  ,"                        May increase performance significantly."
  ,"  no-hole-cxt           Turns off printing local contexts of holes."
  ]

elabPath :: FilePath -> String -> IO ()
elabPath path args = mainWith (pure $ path : words args)

mainInteraction :: IO ()
mainInteraction = mainWith getArgs

frc0 :: Val -> Val
frc0 = let ?cof = emptyNCof; ?dom = 0 in frc
{-# inline frc0 #-}

quote0Frozen :: Frozen -> Tm
quote0Frozen f =
  let ?cof = emptyNCof; ?dom = 0; ?trace = True; ?opt = QDontUnfold in quoteFrozen f
{-# inline quote0Frozen #-}

quote0 :: Quote a b => a -> b
quote0 = let ?cof = emptyNCof; ?dom = 0; ?opt = QDontUnfold in quote
{-# inline quote0 #-}

tracingCommands :: IO ()
tracingCommands = do
  putStrLn "Tracing commands:"
  putStrLn "  ENTER                  proceed one step"
  putStrLn "  skip ENTER             print final value"
  putStrLn "  skip <number> ENTER    skip given number of steps"
  putStrLn "  trace ENTER            print all steps until final value"
  putStrLn "  trace <number> ENTER   proceed given number of steps"
  putStrLn "  help ENTER             print this message"

traceUnfold :: Val -> Int -> Int -> Bool -> IO ()
traceUnfold v batch i silent = case frc0 v of
  VUnf f v v' -> do
    if batch <= 0 then do
      putStrLn $ pretty0 $ quote0Frozen v
      putStrLn $ "STEP " ++ show (i + 1) ++ ", NEXT UNFOLDING: " ++ show (f^.name)
      let getCommand = do
             l <- words <$> getLine
             let retry = do
                   putStrLn "Invalid input"
                   tracingCommands
                   getCommand
             case l of
               [] ->
                 traceUnfold v' 0 (i + 1) False
               ["trace"] ->
                 traceUnfold v' maxBound (i + 1) False
               ["trace", n] -> case readMaybe n of
                 Just n  | n > 0 -> traceUnfold v' (n - 1) (i + 1) False
                 _               -> retry
               ["skip"] -> do
                 traceUnfold v' maxBound (i + 1) True
               ["skip", n] -> case readMaybe n of
                 Just n | n > 0 -> traceUnfold v' (n - 1) (i + 1) True
                 _              -> retry
               ["help"] -> do
                 tracingCommands
                 getCommand
               _ ->
                 retry
      getCommand
    else do
      unless silent $ do
        putStrLn $ pretty0 $ quote0Frozen v
        putStrLn $ "STEP " ++ show (i + 1)
        putStrLn ""
      traceUnfold v' (batch - 1) (i + 1) silent
  v -> do
    putStrLn $ pretty0 $ quote0 v
    putStrLn $ "FINISHED AT STEP " ++ show (i + 1)

parseArgs :: [String]
       -> IO (FilePath, Maybe String, Maybe String, Maybe String, Bool, Bool, Bool, Bool)
parseArgs args = do
  let exit = putStrLn helpMsg >> exitSuccess
  (path, args) <- case args of
    path:args -> pure (path, args)
    _         -> exit
  (printnf, args) <- case args of
    "nf":def:args -> pure (Just def, args)
    args          -> pure (Nothing, args)
  (trace, args) <- case args of
    "trace":def:args -> pure (Just def, args)
    args             -> pure (Nothing, args)
  (printty, args) <- case args of
    "ty":def:args -> pure (Just def, args)
    args          -> pure (Nothing, args)
  (elab, args) <- case args of
    "elab":args -> pure (True, args)
    args        -> pure (False, args)
  (verbose, args) <- case args of
    "verbose":args -> pure (True, args)
    args           -> pure (False, args)
  (unfold, args) <- case args of
    "unfold":args -> pure (True, args)
    args          -> pure (False, args)
  holeCxts <- case args of
    "no-hole-cxts":[] -> pure False
    []                -> pure True
    _                 -> exit
  pure (path, printnf, trace, printty, elab, verbose, unfold, holeCxts)

mainWith :: IO [String] -> IO ()
mainWith getArgs = do
  resetElabState
  resetStats
  (path, printnf, trace, printty, printelab, verbosity, unfold, holeCxts) <- parseArgs =<< getArgs

  unfold <- pure $ isJust printnf || unfold

  modState $
      (printingOpts %~ (verbose      .~ verbosity)
                     . (showHoleCxts .~ holeCxts))
    . (unfolding .~ unfold)


  (_, !totaltime) <- timed (elaborate path)
  st <- getState
  putStrLn ""
  putStrLn ("parsing time: " ++ show (st^.parsingTime))
  putStrLn ("elaboration time: " ++ show (totaltime - st^.parsingTime))
  putStrLn ("checked " ++ show (st^.lvl) ++ " definitions")

  when printelab do
    putStrLn ("\n------------------------------------------------------------")
    putStrLn ("------------------------------------------------------------")
    putStrLn $ pretty0 (st^.top')

  case printnf of
    Just x -> do
      (!nf, !nftime) <- case M.lookup (FP.strToUtf8 x) (st^.top) of
        Just (TEDef i) -> do
          let ?env = ENil; ?cof = emptyNCof; ?dom = 0
          timedPure (quoteUnfold (i^.defVal))
        _ -> do
          putStrLn $ "No top-level definition with name: " ++ show x
          exitSuccess
      putStrLn ("------------------------------------------------------------")
      putStrLn ("------------------------------------------------------------")
      putStrLn ""
      putStrLn $ "Normal form of " ++ x ++ ":\n\n" ++ pretty0 nf
      putStrLn ""
      putStrLn $ "Normalized in " ++ show nftime
    Nothing ->
      pure ()

  case trace of
    Just x -> do
      v <- case M.lookup (FP.strToUtf8 x) (st^.top) of
        Just (TEDef i) ->
          pure $! i^.defVal
        _ -> do
          putStrLn $ "No top-level definition with name: " ++ show x
          exitSuccess
      putStrLn ""
      tracingCommands
      putStrLn ""
      traceUnfold v 0 0 False
    Nothing ->
      pure ()

  case printty of
    Just x -> do
      case M.lookup (FP.strToUtf8 x) (st^.top) of
        Just (TEDef i) -> do
          putStrLn ""
          putStrLn $ show (i^.pos)
          putStrLn $ x ++ " : " ++ pretty0 (i^.defTy)
        _ -> do
          putStrLn $ "No top-level definition with name: " ++ show x
          exitSuccess
    Nothing ->
      pure ()

  renderStats
