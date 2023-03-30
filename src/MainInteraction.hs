
module MainInteraction where

import System.Environment
import System.Exit

import Common
import CoreTypes
import Elaboration
import ElabState
import Pretty

helpMsg = unlines [
   "usage: cctt <file> [nf <topdef>] [elab] [verbose]"
  ,""
  ,"Checks <file>. Options:"
  ,"  nf <topdef>   prints the normal form of top-level definition <topdef>"
  ,"  elab          prints the elaboration output"
  ,"  verbose       prints path endpoints and hcom types explicitly"
  ]

elabPath :: FilePath -> [String] -> IO ()
elabPath path args = mainWith (pure $ path : args)

mainInteraction :: IO ()
mainInteraction = mainWith getArgs

parseArgs :: [String] -> IO (FilePath, Maybe Name, Bool, Bool)
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
  verbose <- case args of
    "verbose":[] -> pure True
    []           -> pure False
    _            -> exit
  pure (path, printnf, elab, verbose)


mainWith :: IO [String] -> IO ()
mainWith getArgs = do
  resetTop
  (path, printnf, printelab, verbosity) <- parseArgs =<< getArgs

  modTop $
      (verbose .~ verbosity)
    . (printNf .~ printnf)

  (top, totaltime) <- timed (elaborate path)
  parsetime <- getTop <&> (^.parsingTime)

  putStrLn (path ++ " checked in " ++ show totaltime)
  putStrLn ("parsing time: " ++ show parsetime)
  putStrLn ("checked " ++ show (topLen top) ++ " definitions")

  when printelab do
    putStrLn ""
    putStrLn $ pretty top
  pure ()
