module Common (
    module Common
  , module Control.Monad
  , module Data.Bits
  , module Lens.Micro
  , module Lens.Micro.TH
  , module Data.IORef
  , module GHC.Exts
  , module GHC.Word
  , module Text.Show
  , module Data.Foldable
  , FP.utf8ToStr
  , FP.strToUtf8
  , runIO
  , trace
  , traceM
  , traceShow
  , traceShowM) where

import Control.Monad
import Data.Bits
import Data.List
import Data.Time.Clock
import GHC.Exts hiding (lazy, fromList, toList)
import Lens.Micro
import Lens.Micro.TH
import Data.IORef
import Data.Foldable
import Debug.Trace (trace, traceM, traceShow, traceShowM)
import Data.Flat
import IO (runIO)
import GHC.IO
import GHC.Word
import Text.Show

import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Internal as B
import qualified FlatParse.Stateful as FP

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

data Name
  = NSpan {-# unpack #-} Span
  | NGeneric B.ByteString
  | N_
  deriving (Eq, Ord)

instance Show Name where
  show (NSpan x)    = show x
  show (NGeneric x) = B.unpack x
  show N_           = "_"

nameToBs :: Name -> B.ByteString
nameToBs = \case
  NSpan x    -> spanToBs x
  NGeneric x -> x
  N_         -> "_"

a_ = NGeneric "a"
b_ = NGeneric "b"
c_ = NGeneric "c"
d_ = NGeneric "d"
e_ = NGeneric "e"
f_ = NGeneric "f"
g_ = NGeneric "g"
h_ = NGeneric "h"
i_ = NGeneric "i"
j_ = NGeneric "j"
k_ = NGeneric "k"
l_ = NGeneric "l"
m_ = NGeneric "m"
n_ = NGeneric "n"
o_ = NGeneric "o"
p_ = NGeneric "p"
q_ = NGeneric "q"
r_ = NGeneric "r"
s_ = NGeneric "s"
t_ = NGeneric "t"
u_ = NGeneric "u"
x_ = NGeneric "x"
y_ = NGeneric "y"
z_ = NGeneric "z"
linv_ = NGeneric "linv"
rinv_ = NGeneric "rinv"
coh_ = NGeneric "coh"
ty_ = NGeneric "Ty_"

----------------------------------------------------------------------------------------------------

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

ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (reallyUnsafePtrEquality# x y)
{-# inline ptrEq #-}

-- De Bruijn indices and levels
--------------------------------------------------------------------------------

newtype Ix = Ix {unIx :: Word}
  deriving (Eq, Ord, Show, Num, Enum, Bits, Integral, Real) via Word

newtype Lvl = Lvl {unLvl :: Word}
  deriving (Eq, Ord, Show, Num, Enum, Bits, Integral, Real) via Word

newtype IVar = IVar# {unIVar :: Word}
  deriving (Eq, Ord, Show, Num, Enum, Bits, Integral, Real, Flat) via Word

class HasDom s where
  dom    :: s -> IVar
  setDom :: IVar -> s -> s

class HasCod s where
  cod    :: s -> IVar
  setCod :: IVar -> s -> s

class Lift a where
  lift :: a -> a

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


-- Source descriptors, positions, spans
--------------------------------------------------------------------------------

-- | Describes a source bytestring such that a position can point into it.
data Src
  = SrcFile FilePath B.ByteString -- ^ Concrete source file.
  | SrcImpossible                 -- ^ Impossible case just for killing unboxing.

instance Show Src where
  show (SrcFile fp _) = "File " ++ fp
  show  SrcImpossible = impossible

srcToBs :: Src -> B.ByteString
srcToBs (SrcFile _ bs)   = bs
srcToBs SrcImpossible    = impossible

-- | Equality of bytestrings by reference, used for sanity checks.
samePtr :: B.ByteString -> B.ByteString -> Bool
samePtr x y = case B.toForeignPtr x of
  (x, _, _) -> case B.toForeignPtr y of
    (y, _, _) -> x == y
{-# inline samePtr #-}

-- | Equality of sources only checks that underlying bytestrings have the same
--   underlying data.
instance Eq Src where
  SrcFile _ s   == SrcFile _ s'   = samePtr s s'
  _             == _              = impossible

-- | Source position. We decorate raw terms with this.
data Pos = Pos Src FP.Pos
  deriving Show via DontShow Pos
  deriving Eq

data ParsedPos = ParsedPos FilePath String Int Int

parsePos :: Pos -> ParsedPos
parsePos (Pos src p) = case src of
  SrcImpossible    -> impossible
  SrcFile path src -> case FP.posLineCols src [p] of
    [(l, c)] -> let f = FP.utf8ToStr src in ParsedPos path f l c
    _        -> impossible

instance Show ParsedPos where
  show (ParsedPos path _ linum colnum) =
    path ++ ":"  ++ show (linum  + 1) ++ ":" ++ show colnum

rawPos :: Pos -> FP.Pos
rawPos (Pos _ p) = p

initialPos :: Src -> Pos
initialPos src = Pos src (FP.Pos 0)

instance Ord Pos where
  compare (Pos src i) (Pos src' i')
    | src == src' = compare i i'
    | otherwise   = impossible

  (<) (Pos src i) (Pos src' i')
    | src == src' = i < i'
    | otherwise   = impossible

  (<=) (Pos src i) (Pos src' i')
    | src == src' = i <= i'
    | otherwise   = impossible

-- | Source span. The left position must not be larger than the right one.
data Span = Span# Src FP.Pos FP.Pos
  -- deriving Show via DontShow Span

instance Show Span where
  show = spanToString

pattern Span :: Pos -> Pos -> Span
pattern Span x y <- ((\(Span# src x y) -> (Pos src x, Pos src y)) -> (x, y)) where
  Span (Pos src x) (Pos src' y)
    | src == src' && x <= y = Span# src x y
    | otherwise             = impossible
{-# complete Span #-}

spanToBs :: Span -> B.ByteString
spanToBs (Span (Pos src i) (Pos _ j)) =
  let bstr = srcToBs src
      i'   = B.length bstr - coerce i   -- Pos counts backwards from the end of the string
      j'   = B.length bstr - coerce j
  in B.take (j' - i') (B.drop i' bstr)

instance Eq Span where
  x == y = spanToBs x == spanToBs y

instance Ord Span where
  compare x y = compare (spanToBs x) (spanToBs y)

spanToString :: Span -> String
spanToString s = FP.utf8ToStr (spanToBs s)
