
module MainInteraction where

import System.Environment
import System.Exit

import Common
import CoreTypes
import Elaboration
import Parser
import Pretty

-- | Elaborate a string, render output.
elabString :: String -> IO ()
elabString str = do
  top <- parseString "(interactive)" str
  top <- elabTop Nothing "(interactive)" str top
  putStrLn $ pretty top

helpMsg = unlines [
   "usage: cctt <file> [nf <topdef>] [elab]"
  ,""
  ,"Checks <file>. Options:"
  ,"  nf <topdef>   prints the normal form of top-level definition <topdef>"
  ,"  elab          prints the elaboration output"
  ]

elabFile :: FilePath -> IO ()
elabFile path = mainWith (pure [path])

mainInteraction :: IO ()
mainInteraction = mainWith getArgs

mainWith :: IO [String] -> IO ()
mainWith getArgs = do
  args <- getArgs
  (path, printnf, printelab) <- case args of
    [path]                      -> pure (path, Nothing, False)
    path:"nf":printnf:[]        -> pure (path, Just printnf, False)
    path:"nf":printnf:"elab":[] -> pure (path, Just printnf, True)
    path:"elab":[]              -> pure (path, Nothing, True)
    _                           -> putStrLn helpMsg >> exitSuccess
  file <- readFile path
  (top, tparse) <- timed (parseString path file)
  putStrLn (path ++ " parsed in " ++ show tparse)
  (top, tcheck) <- timed (elabTop printnf path file top)
  putStrLn (path ++ " checked in " ++ show tcheck)
  putStrLn ("loaded " ++ show (topLen top) ++ " definitions")
  putStrLn ("total load time: " ++ show (tparse + tcheck))
  when printelab do
    putStrLn ""
    putStrLn $ pretty top
  pure ()
