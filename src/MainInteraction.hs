
module MainInteraction where

import qualified Data.Map.Strict as M
import System.Environment
import System.Exit

import Common
import CoreTypes
import ElabState
import Elaboration
import Interval
import Pretty
import Quotation

#ifdef RUNTIMESTATS
import Statistics
import qualified Data.Ref.F as RF
#endif

helpMsg = unlines [
   "usage: cctt <file> [nf <topdef>] [ty <topdef>] [elab] [verbose] [no-hole-cxts]"
  ,""
  ,"Checks <file>. Options:"
  ,"  nf <topdef>   prints the normal form of top-level definition <topdef>"
  ,"  ty <topdef>   prints the type of the top-level definition <topdef>"
  ,"  elab          prints the elaboration output"
  ,"  verbose       prints path endpoints, hcom types and hole source positions explicitly"
  ,"  no-hole-cxt   turn off printing local contexts of holes"
  ]

elabPath :: FilePath -> String -> IO ()
elabPath path args = mainWith (pure $ path : words args)

mainInteraction :: IO ()
mainInteraction = mainWith getArgs

parseArgs :: [String] -> IO (FilePath, Maybe Name, Maybe Name, Bool, Bool, Bool)
parseArgs args = do
  let exit = putStrLn helpMsg >> exitSuccess
  (path, args) <- case args of
    path:args -> pure (path, args)
    _         -> exit
  (printnf, args) <- case args of
    "nf":def:args -> pure (Just def, args)
    args          -> pure (Nothing, args)
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
  pure (path, printnf, printty, elab, verbose, holeCxts)

mainWith :: IO [String] -> IO ()
mainWith getArgs = do
  resetElabState
#ifdef RUNTIMESTATS
  resetStats
#endif
  (path, printnf, printty, printelab, verbosity, holeCxts) <- parseArgs =<< getArgs

  modState $ printingOpts %~
      (verbose .~ verbosity)
    . (printNf .~ printnf)
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
      (!nf, !nftime) <- case M.lookup x (st^.top) of
        Just (TEDef i) -> do
          let ?env = ENil; ?cof = idSub 0; ?dom = 0
          timedPure (quote (i^.defVal))
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

  case printty of
    Just x -> do
      case M.lookup x (st^.top) of
        Just (TEDef i) -> do
          putStrLn ""
          putStrLn $ sourcePosPretty (i^.pos)
          putStrLn $ x ++ " : " ++ pretty0 (i^.defTy)
        _ -> do
          putStrLn $ "No top-level definition with name: " ++ show x
          exitSuccess
    Nothing ->
      pure ()

#ifdef RUNTIMESTATS
  hcs  <- RF.read hcomStat
  ehcs <- RF.read emptyhcomStat
  maxi <- RF.read maxIVarStat
  bs   <- RF.read blockStat
  ubs  <- RF.read unblockStat
  putStrLn $ "Total hcom calls: " ++ show hcs
  putStrLn $ "Non-diagonal empty hcom calls: " ++ show ehcs
  putStrLn $ "Empty hcom ratio: " ++ show (fromIntegral ehcs / (fromIntegral hcs :: Double))
  putStrLn $ "Largest interval scope size: " ++ show maxi
  putStrLn $ "Total neutral forcings: " ++ show (bs + ubs)
  putStrLn $ "Of which blocked: " ++ show bs
#endif
