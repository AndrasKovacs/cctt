module Common (
    module Common
  , module Control.Monad
  , module Data.Bits
  , module Lens.Micro.Platform
  , module Data.IORef
  , module GHC.Exts
  , SourcePos(..)
  , sourcePosPretty
  , initialPos
  , Pos
  , unPos
  , runIO
  , trace
  , traceM
  , traceShow
  , traceShowM) where

import Control.Monad
import Data.Bits
import Data.List
import Data.Time.Clock
import GHC.Exts hiding (lazy, fromList)
import Lens.Micro.Platform
import Text.Megaparsec (SourcePos(..), sourcePosPretty, initialPos, Pos, unPos)
import Data.IORef
import Debug.Trace (trace, traceM, traceShow, traceShowM)
import Data.Flat
import IO (runIO)
import GHC.IO

-- Debug printing, toggled by "debug" cabal flag
--------------------------------------------------------------------------------

#define DEBUG

#ifdef DEBUG
import GHC.Stack
#endif

#ifdef DEBUG
type Dbg = HasCallStack

debug :: [String] -> IO ()
debug strs = putStrLn (intercalate " | " strs ++ " END")

debugging :: IO () -> IO ()
debugging act = act
{-# inline debugging #-}
#else
type Dbg = () :: Constraint

debug :: [String] -> IO ()
debug strs = pure ()
{-# inline debug #-}

debugging :: IO () -> IO ()
debugging _ = pure ()
{-# inline debugging #-}
#endif

debug' :: [String] -> IO ()
debug' strs = putStrLn (intercalate " | " strs ++ " END")

debugging' :: IO () -> IO ()
debugging' act = act
{-# inline debugging' #-}

--------------------------------------------------------------------------------

noinlineRunIO :: IO a -> a
noinlineRunIO (IO f) = runRW# (\s -> case f s of (# _, a #) -> a)
{-# noinline noinlineRunIO #-}

type Name = String

uf :: Dbg => a
uf = undefined
{-# noinline uf #-}

impossible :: Dbg => a
impossible = error "impossible"
{-# noinline impossible #-}

ctz :: Word -> Word
ctz (W# n) = W# (ctz# n)
{-# inline ctz #-}

clz :: Word -> Word
clz (W# n) = W# (clz# n)
{-# inline clz #-}

i2w :: Int -> Word
i2w (I# n) = W# (int2Word# n)
{-# inline i2w #-}

w2i :: Word -> Int
w2i (W# n) = I# (word2Int# n)
{-# inline w2i #-}

($$!) :: (a -> b) -> a -> b
($$!) f a = f $! a
{-# inline ($$!) #-}
infixl 9 $$!

infixl 4 <*!>
(<*!>) :: Monad m => m (a -> b) -> m a -> m b
(<*!>) mf ma = do
  f <- mf
  a <- ma
  pure $! f a
{-# inline (<*!>) #-}

infixr 4 //
(//) :: a -> b -> (a, b)
a // b = (a, b)
{-# inline (//) #-}

-- De Bruijn indices and levels
--------------------------------------------------------------------------------

newtype Ix = Ix {unIx :: Word}
  deriving (Eq, Ord, Show, Num, Enum, Bits, Integral, Real) via Word

newtype Lvl = Lvl {unLvl :: Word}
  deriving (Eq, Ord, Show, Num, Enum, Bits, Integral, Real) via Word

newtype IVar = IVar# {unIVar :: Word}
  deriving (Eq, Ord, Show, Num, Enum, Bits, Integral, Real, Flat) via Word

lvlToIx :: Lvl -> Lvl -> Ix
lvlToIx (Lvl envl) (Lvl x) = Ix (envl - x - 1)
{-# inline lvlToIx #-}

ixToLvl :: Lvl -> Ix -> Lvl
ixToLvl (Lvl envl) (Ix x) = Lvl (envl - x - 1)
{-# inline ixToLvl #-}

type LvlArg = (?lvl :: Lvl)


-- Not printing stuff
--------------------------------------------------------------------------------

newtype DontShow a = DontShow {unDontShow :: a} deriving Eq

instance Show (DontShow a) where
  showsPrec _ _ x = x

--------------------------------------------------------------------------------

data Box a = Box ~a deriving Show

-- Time measurement
--------------------------------------------------------------------------------

-- | Time an IO computation. Result is forced to whnf.
timed :: IO a -> IO (a, NominalDiffTime)
timed a = do
  t1  <- getCurrentTime
  res <- a
  t2  <- getCurrentTime
  let diff = diffUTCTime t2 t1
  pure (res, diff)
{-# inline timed #-}

-- | Time a lazy pure value. Result is forced to whnf.
timedPure :: a -> IO (a, NominalDiffTime)
timedPure ~a = do
  t1  <- getCurrentTime
  let res = a
  t2  <- getCurrentTime
  let diff = diffUTCTime t2 t1
  pure (res, diff)
{-# noinline timedPure #-}

-- | Time a lazy pure value. Result is forced to whnf.
timedPure_ :: a -> IO NominalDiffTime
timedPure_ ~a = do
  t1  <- getCurrentTime
  seq a $ do
    t2  <- getCurrentTime
    let diff = diffUTCTime t2 t1
    pure diff
{-# noinline timedPure_ #-}
