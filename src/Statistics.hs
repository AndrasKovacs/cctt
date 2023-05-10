
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

#ifdef RUNTIMESTATS
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
  if isEmpty then bumpEmptyHCom else pure ()

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
  putStrLn $ "Non-diagonal empty hcom calls: " ++ show ehcs
  putStrLn $ "Empty hcom ratio: " ++ show (fromIntegral ehcs / (fromIntegral hcs :: Double))
  putStrLn $ "Largest interval scope size: " ++ show maxi
  putStrLn $ "Total neutral forcings: " ++ show (bs + ubs)
  putStrLn $ "Of which blocked: " ++ show bs
#else

bumpHCom :: IO ()
bumpHCom = pure ()
{-# inline bumpHCom #-}

bumpMaxIVar :: IVar -> IO ()
bumpMaxIVar i = pure ()
{-# inline bumpMaxIVar #-}

bumpBlock :: IO ()
bumpBlock = pure ()
{-# inline bumpBlock #-}

bumpUnblock :: IO ()
bumpUnblock = pure ()
{-# inline bumpUnblock #-}

bumpEmptyHCom :: IO ()
bumpEmptyHCom = pure ()
{-# inline bumpEmptyHCom #-}

bumpHCom' :: Bool -> IO ()
bumpHCom' _ = pure ()
{-# inline bumpHCom' #-}

#endif

resetStats :: IO ()
resetStats = do
  RF.write hcomStat 0
  RF.write emptyhcomStat 0
  RF.write maxIVarStat 0
  RF.write blockStat 0
  RF.write unblockStat 0

--------------------------------------------------------------------------------
{-

data Stats = Stats {
    statsHComs :: Int
  , statsCoes  :: Int }
  deriving Show

makeFields ''Stats

instance Semigroup Stats where
  Stats x y <> Stats x' y' = Stats (x + x') (y + y')

instance Monoid Stats where
  mempty = Stats 0 0

hcom = Stats 1 0
coe  = Stats 0 1

class GetStats a where
  stats :: a -> Stats

instance GetStats Tm where
  stats = \case
    TopVar{}         -> impossible
    RecursiveCall{}  -> impossible
    LocalVar{}       -> mempty
    Let{}            -> impossible
    TyCon _ ps       -> stats ps
    DCon _ sp        -> stats sp
    HTyCon _ ps      -> stats ps
    HDCon _ _ sp _   -> stats sp
    HCase t _ b _ cs -> stats t <> stats b <> stats cs
    HSplit{}         -> impossible
    Case t _ b _ cs  -> stats t <> stats b <> stats cs
    Split{}          -> impossible
    Pi _ a b         -> stats a <> stats b
    App t u          -> stats t <> stats u
    Lam _ t          -> stats t
    Sg _ a b         -> stats a <> stats b
    Pair _ t u       -> stats t <> stats u
    Proj1 t _        -> stats t
    Proj2 t _        -> stats t
    Wrap _ t         -> stats t
    Pack _ t         -> stats t
    Unpack t _       -> stats t
    U                -> mempty
    Path x a t u     -> stats a <> stats t <> stats u
    PApp l r t i     -> stats l <> stats r <> stats t
    PLam l r _ t     -> stats l <> stats r <> stats t
    Line x a         -> stats a
    LApp t _         -> stats t
    LLam _ t         -> stats t
    Coe _ _ _ a t    -> coe <> stats a <> stats t
    HCom _ _ a sys t -> hcom <> stats a <> stats sys <> stats t
    GlueTy a sys     -> stats a <> stats sys
    Glue t sys fibs  -> stats t <> stats sys <> stats fibs
    Unglue t _       -> stats t
    Hole{}           -> mempty
    Com{}            -> impossible
    WkI{}            -> impossible
    Refl{}           -> impossible
    Sym{}            -> impossible
    Trans{}          -> impossible
    Ap{}             -> impossible

instance GetStats Cases where
  stats = \case
    CSNil           -> mempty
    CSCons _ _ t cs -> stats t <> stats cs

instance GetStats HCases where
  stats = \case
    HCSNil             -> mempty
    HCSCons _ _ _ t cs -> stats t <> stats cs

instance GetStats Sys where
  stats = \case
    SEmpty          -> mempty
    SCons cof t sys -> stats t <> stats sys

instance GetStats SysHCom where
  stats = \case
    SHEmpty            -> mempty
    SHCons cof x t sys -> stats t <> stats sys

instance GetStats Spine where
  stats = \case
    SPNil       -> mempty
    SPCons t sp -> stats t <> stats sp
-}
