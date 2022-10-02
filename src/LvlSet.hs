
-- | Level sets (limited to 64 entries).

module LvlSet where

import Data.Foldable
import Common

newtype LvlSet = LvlSet Int deriving (Eq, Bits) via Int

instance Semigroup LvlSet where
  (<>) = (.|.)
  {-# inline (<>) #-}

instance Monoid LvlSet where
  mempty = LvlSet 0
  {-# inline mempty #-}

insert :: Lvl -> LvlSet -> LvlSet
insert (Lvl x) (LvlSet s) = LvlSet (unsafeShiftL 1 x .|. s)
{-# inline insert #-}

member :: Lvl -> LvlSet -> Bool
member (Lvl x) (LvlSet s) = (unsafeShiftL 1 x .&. s) /= 0
{-# inline member #-}

toList :: LvlSet -> [Lvl]
toList s = filter (`member` s) (coerce [0..63::Int])

fromList :: [Lvl] -> LvlSet
fromList = foldl' (flip insert) mempty

instance Show LvlSet where
  show = show . LvlSet.toList
