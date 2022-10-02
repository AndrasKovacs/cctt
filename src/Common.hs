module Common (
    module Common
  , module Data.Bits
  , coerce) where

import GHC.Exts
import Data.List
import Data.Bits

#ifdef DEBUG
import GHC.Stack
#endif

-- Debug printing, toggled by "debug" cabal flag
--------------------------------------------------------------------------------

-- define DEBUG

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

uf :: Dbg => a
uf = undefined
{-# noinline uf #-}

impossible :: Dbg => a
impossible = error "impossible"
{-# noinline impossible #-}


-- De Bruijn indices and levels
--------------------------------------------------------------------------------

newtype Ix = Ix {unIx :: Int}
  deriving (Eq, Ord, Show, Num, Enum, Bits) via Int

newtype Lvl = Lvl {unLvl :: Int}
  deriving (Eq, Ord, Show, Num, Enum, Bits) via Int

newtype IVar = IVar# {unIVar :: Int}
  deriving (Eq, Ord, Show, Num, Enum, Bits) via Int

lvlToIx :: Lvl -> Lvl -> Ix
lvlToIx (Lvl envl) (Lvl x) = Ix (envl - x - 1)
{-# inline lvlToIx #-}

type LvlArg = (?lvl :: Lvl)

-- Not printing stuff
--------------------------------------------------------------------------------

newtype DontPrint a = DontPrint a

instance Show (DontPrint a) where
  showsPrec _ _ x = x
