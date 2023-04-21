
module MainInteraction where

import System.Environment
import System.Exit
import Common
import Elaboration
import ElabState
import Pretty

helpMsg = unlines [
   "usage: cctt <file> [nf <topdef>] [elab] [verbose] [no-hole-cxts]"
  ,""
  ,"Checks <file>. Options:"
  ,"  nf <topdef>   prints the normal form of top-level definition <topdef>"
  ,"  elab          prints the elaboration output"
  ,"  verbose       prints path endpoints and hcom types explicitly"
  ,"  no-hole-cxt   turn off printing local contexts of holes"
  ]

elabPath :: FilePath -> String -> IO ()
elabPath path args = mainWith (pure $ path : words args)

mainInteraction :: IO ()
mainInteraction = mainWith getArgs

parseArgs :: [String] -> IO (FilePath, Maybe Name, Bool, Bool, Bool)
parseArgs args = do
  let exit = putStrLn helpMsg >> exitSuccess
  (path, args) <- case args of
    path:args -> pure (path, args)
    _         -> exit
  (printnf, args) <- case args of
    "nf":printnf:args -> pure (Just printnf, args)
    args              -> pure (Nothing, args)
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
  pure (path, printnf, elab, verbose, holeCxts)


mainWith :: IO [String] -> IO ()
mainWith getArgs = do
  reset
  (path, printnf, printelab, verbosity, holeCxts) <- parseArgs =<< getArgs

  modState $ printingOpts %~
      (verbose .~ verbosity)
    . (printNf .~ printnf)
    . (showHoleCxts .~ holeCxts)

  (!top, !totaltime) <- timed (elaborate path)
  st <- getState
  putStrLn (path ++ " checked in " ++ show totaltime)
  putStrLn ("parsing time: " ++ show (st^.parsingTime))
  putStrLn ("checked " ++ show (st^.lvl) ++ " definitions")

  when printelab do
    putStrLn $ pretty0 (st^.top')
