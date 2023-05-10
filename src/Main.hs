
module Main where

import MainInteraction
import Control.Exception

#ifdef RUNTIMESTATS
import Statistics
#endif

#ifdef RUNTIMESTATS
main :: IO ()
main = do
  catch mainInteraction \case
    UserInterrupt -> renderStats
    e             -> throw e
#else
main :: IO ()
main = mainInteraction
#endif
