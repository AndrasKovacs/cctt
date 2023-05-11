
module Statistics where

import Common
import qualified Data.Ref.F as RF

--------------------------------------------------------------------------------

hcomStat :: RF.Ref Int
hcomStat = runIO $ RF.new 0
{-# noinline hcomStat #-}

emptyhcomStat :: RF.Ref Int
emptyhcomStat = runIO $ RF.new 0
{-# noinline emptyhcomStat #-}

maxIVarStat :: RF.Ref IVar
maxIVarStat = runIO $ RF.new 0
{-# noinline maxIVarStat #-}

blockStat :: RF.Ref Int
blockStat = runIO $ RF.new 0
{-# noinline blockStat #-}

unblockStat :: RF.Ref Int
unblockStat = runIO $ RF.new 0
{-# noinline unblockStat #-}

------------------------------------------------------------

bumpHCom :: IO ()
bumpHCom = RF.modify hcomStat (+1)

bumpMaxIVar :: IVar -> IO ()
bumpMaxIVar i = do
  m <- RF.read maxIVarStat
  RF.write maxIVarStat (max i m)

bumpBlock :: IO ()
bumpBlock = RF.modify blockStat (+1)

bumpUnblock :: IO ()
bumpUnblock = RF.modify unblockStat (+1)

bumpEmptyHCom :: IO ()
bumpEmptyHCom = RF.modify emptyhcomStat (+1)

bumpHCom' :: Bool -> IO ()
bumpHCom' isEmpty = do
  bumpHCom
#ifdef EMPTYHCOMSTATS
  if isEmpty then bumpEmptyHCom else pure ()
#endif

{-# inline bumpHCom #-}
{-# inline bumpMaxIVar #-}
{-# inline bumpBlock #-}
{-# inline bumpUnblock #-}
{-# inline bumpEmptyHCom #-}
{-# inline bumpHCom' #-}

renderStats :: IO ()
renderStats = do
  hcs  <- RF.read hcomStat
  ehcs <- RF.read emptyhcomStat
  maxi <- RF.read maxIVarStat
  bs   <- RF.read blockStat
  ubs  <- RF.read unblockStat
  putStrLn $ "Total hcom calls: " ++ show hcs
#ifdef EMPTYHCOMSTATS
  putStrLn $ "Non-diagonal empty hcom calls: " ++ show ehcs
  putStrLn $ "Empty hcom ratio: " ++ show (fromIntegral ehcs / (fromIntegral hcs :: Double))
#endif
  putStrLn $ "Largest interval scope size: " ++ show maxi
  putStrLn $ "Total neutral forcings: " ++ show (bs + ubs)
  putStrLn $ "Of which blocked: " ++ show bs

resetStats :: IO ()
resetStats = do
  RF.write hcomStat 0
  RF.write emptyhcomStat 0
  RF.write maxIVarStat 0
  RF.write blockStat 0
  RF.write unblockStat 0
