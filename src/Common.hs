module Common (
    module Common
  , module Data.Bits
  , module Lens.Micro.Platform
  , coerce) where

import GHC.Exts
import Data.List
import Data.Bits
import Lens.Micro.Platform

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

infixl 4 <$!>
(<$!>) :: Monad m => (a -> b) -> m a -> m b
(<$!>) f ma = do
  a <- ma
  pure $! f a
{-# inline (<$!>) #-}

-- De Bruijn indices and levels
--------------------------------------------------------------------------------

newtype Ix = Ix {unIx :: Word}
  deriving (Eq, Ord, Show, Num, Enum, Bits, Integral, Real) via Word

newtype Lvl = Lvl {unLvl :: Word}
  deriving (Eq, Ord, Show, Num, Enum, Bits, Integral, Real) via Word

newtype IVar = IVar# {unIVar :: Word}
  deriving (Eq, Ord, Show, Num, Enum, Bits, Integral, Real) via Word

lvlToIx :: Lvl -> Lvl -> Ix
lvlToIx (Lvl envl) (Lvl x) = Ix (envl - x - 1)
{-# inline lvlToIx #-}

type LvlArg = (?lvl :: Lvl)

-- Not printing stuff
--------------------------------------------------------------------------------

newtype DontShow a = DontShow a

instance Show (DontShow a) where
  showsPrec _ _ x = x
