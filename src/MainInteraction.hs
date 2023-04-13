
module MainInteraction where

import System.Environment
import System.Exit

import Common
import CoreTypes
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

elabPath :: FilePath -> [String] -> IO ()
elabPath path args = mainWith (pure $ path : args)

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
  noHoleCxts <- case args of
    "no-hole-cxts":[] -> pure True
    []                -> pure False
    _                 -> exit
  pure (path, printnf, elab, verbose, noHoleCxts)


mainWith :: IO [String] -> IO ()
mainWith getArgs = do
  resetTop
  (path, printnf, printelab, verbosity, noHoleCxts) <- parseArgs =<< getArgs

  modTop (printingOpts %~ ((verbose .~ verbosity) . (printNf .~ printnf)))

  (top, totaltime) <- timed (elaborate path)
  parsetime <- getTop <&> (^.parsingTime)

  putStrLn (path ++ " checked in " ++ show totaltime)
  putStrLn ("parsing time: " ++ show parsetime)
  putStrLn ("checked " ++ show (topLen top) ++ " definitions")

  when printelab do
    putStrLn $ pretty top
  pure ()
