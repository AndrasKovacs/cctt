
module MainInteraction where

import System.Environment
import System.Exit

import Common
import CoreTypes
import Elaboration
import ElabState
import Parser
import Pretty

-- | Elaborate a string, render output.
elabString :: String -> IO ()
elabString str = do
  let path = "(interactive)"
  raw <- parseString path str
  modTop ((currentPath .~ path)
        . (currentSrc .~ str))
  out <- elabTop raw
  putStrLn $ pretty out

helpMsg = unlines [
   "usage: cctt <file> [nf <topdef>] [elab] [verbose]"
  ,""
  ,"Checks <file>. Options:"
  ,"  nf <topdef>   prints the normal form of top-level definition <topdef>"
  ,"  elab          prints the elaboration output"
  ,"  verbose       prints path endpoints and hcom types explicitly"
  ]

elabFile :: FilePath -> [String] -> IO ()
elabFile path args = mainWith (pure $ path : args)

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

  file          <- readFile path
  (top, tparse) <- timed (parseString path file)
  putStrLn (path ++ " parsed in " ++ show tparse)

  modTop $
      (verbose .~ verbosity)
    . (currentPath .~ path)
    . (currentSrc .~ file)
    . (printNf .~ printnf)
  (top, tcheck) <- timed (elabTop top)
  putStrLn (path ++ " checked in " ++ show tcheck)
  putStrLn ("checked " ++ show (topLen top) ++ " definitions")
  putStrLn ("total time: " ++ show (tparse + tcheck))
  when printelab do
    putStrLn ""
    putStrLn $ pretty top
  pure ()
