
module Main where

import MainInteraction
import Control.Exception
import Statistics

main :: IO ()
main = do
  catch mainInteraction \case
    UserInterrupt -> renderStats
    e             -> throw e
