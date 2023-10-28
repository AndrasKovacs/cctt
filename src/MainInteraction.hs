
module MainInteraction where

import qualified Data.Map.Strict as M
import System.Environment
import System.Exit
import qualified FlatParse.Stateful as FP
import Text.Read (readMaybe)

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
   "usage: cctt <file> [nf <topdef>] [trace <topdef>] [trace-to-end <topdef>] [ty <topdef>] [elab] [verbose] [no-hole-cxts]"
  ,""
  ,"Checks <file>. Options:"
  ,"  nf <topdef>           prints the normal form of top-level definition <topdef>"
  ,"  trace <topdef>        hit ENTER to interactively step through head unfoldings of a value"
  ,"  trace-to-end <topdef> print all intermediate head unfoldings for a value"
  ,"  ty <topdef>           prints the type of the top-level definition <topdef>"
  ,"  elab                  prints the elaboration output"
  ,"  verbose               prints path endpoints, hcom types and hole source positions explicitly"
  ,"  no-hole-cxt           turn off printing local contexts of holes"
  ]

elabPath :: FilePath -> String -> IO ()
elabPath path args = mainWith (pure $ path : words args)

mainInteraction :: IO ()
mainInteraction = mainWith getArgs

frc0 :: Val -> Val
frc0 = let ?cof = emptyNCof; ?dom = 0 in frc
{-# inline frc0 #-}

quote0 :: Quote a b => a -> b
quote0 = let ?cof = emptyNCof; ?dom = 0 in quoteNoUnfold
{-# inline quote0 #-}

traceUnfold :: Val -> Int -> Int -> Bool -> IO ()
traceUnfold v batch i silent = case frc0 v of
  VUnf inf v v' -> do
    if batch <= 0 then do
      putStrLn $ pretty0 $ quote0 v
      putStrLn $ "STEP " ++ show (i + 1) ++ ": unfolding " ++ show (inf^.name)
      let getCommand = do
             l <- words <$> getLine
             case l of
               []   -> traceUnfold v' 0 (i + 1) False
               [n] -> do
                 let batch = maybe 0 id $ readMaybe n
                 traceUnfold v' (batch - 1) (i + 1) False
               [n, "silent"] -> do
                 let batch = maybe 0 id $ readMaybe n
                 traceUnfold v' (batch - 1) (i + 1) True
               _ -> do
                 putStrLn "invalid input"
                 putStrLn "  - Press ENTER to proceed one step"
                 putStrLn "  - Type \"<number>\" and hit ENTER to proceed forward by that many steps"
                 putStrLn "  - Type \"<number> silent\" to proceed forward without printing"
                 getCommand
      getCommand
    else do
      unless silent $ do
        putStrLn $ pretty0 $ quote0 v
        putStrLn $ "STEP " ++ show (i + 1) ++ ": unfolding " ++ show (inf^.name)
        putStrLn ""
      traceUnfold v' (batch - 1) (i + 1) silent
  v -> do
    putStrLn $ pretty0 $ quote0 v
    putStrLn $ "FINISHED AT STEP " ++ show i

traceToEnd :: Val -> Int -> IO ()
traceToEnd v i = case frc0 v of
  VUnf inf v v' -> do
    putStrLn $ pretty0 $ quote0 v
    putStrLn $ "STEP " ++ show (i + 1) ++ ": unfolding " ++ show (inf^.name)
    traceToEnd v' (i + 1)
  v -> do
    putStrLn $ pretty0 $ quote0 v
    putStrLn $ "STEP " ++ show i

parseArgs :: [String] -> IO (FilePath, Maybe String, Maybe String, Maybe String, Maybe String, Bool, Bool, Bool)
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
  (traceToEnd, args) <- case args of
    "trace-to-end":def:args -> pure (Just def, args)
    args                    -> pure (Nothing, args)
  (printty, args) <- case args of
    "ty":def:args -> pure (Just def, args)
    args          -> pure (Nothing, args)
  (elab, args) <- case args of
    "elab":args -> pure (True, args)
    args        -> pure (False, args)
  (verbose, args) <- case args of
    "verbose":args -> pure (True, args)
    args           -> pure (False, args)
  holeCxts <- case args of
    "no-hole-cxts":[] -> pure False
    []                -> pure True
    _                 -> exit
  pure (path, printnf, trace, traceToEnd, printty, elab, verbose, holeCxts)

mainWith :: IO [String] -> IO ()
mainWith getArgs = do
  resetElabState
  resetStats
  (path, printnf, trace, tracetoend, printty, printelab, verbosity, holeCxts) <- parseArgs =<< getArgs

  modState $ printingOpts %~
      (verbose .~ verbosity)
    . (showHoleCxts .~ holeCxts)

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
      putStrLn "TRACING:"
      putStrLn "  - Press ENTER to proceed one step"
      putStrLn "  - Type \"<number>\" and hit ENTER to proceed forward by that many steps"
      putStrLn "  - Type \"<number> silent\" to proceed forward without printing"
      putStrLn ""
      traceUnfold v 0 0 False
    Nothing ->
      pure ()

  case tracetoend of
    Just x -> do
      v <- case M.lookup (FP.strToUtf8 x) (st^.top) of
        Just (TEDef i) ->
          pure $! i^.defVal
        _ -> do
          putStrLn $ "No top-level definition with name: " ++ show x
          exitSuccess
      traceToEnd v 0
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
