
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

singleton :: Lvl -> LvlSet
singleton x = insert x mempty
{-# inline singleton #-}

insert :: Lvl -> LvlSet -> LvlSet
insert (Lvl x) (LvlSet s) = LvlSet (unsafeShiftL 1 x .|. s)
{-# inline insert #-}

delete :: Lvl -> LvlSet -> LvlSet
delete (Lvl x) (LvlSet s) = LvlSet (complement (unsafeShiftL 1 x) .&. s)
{-# inline delete #-}

member :: Lvl -> LvlSet -> Bool
member (Lvl x) (LvlSet s) = (unsafeShiftL 1 x .&. s) /= 0
{-# inline member #-}

toList :: LvlSet -> [Lvl]
toList = LvlSet.foldr (:) []

fromList :: [Lvl] -> LvlSet
fromList = foldl' (flip insert) mempty

popSmallest :: LvlSet -> (LvlSet -> Lvl -> a) -> a -> a
popSmallest (LvlSet s) success ~fail = case s of
  0 -> fail
  s -> let i = Lvl (ctzInt s) in success (delete i (LvlSet s)) i
{-# inline popSmallest #-}

instance Show LvlSet where
  show = show . LvlSet.toList

foldl :: forall b. (b -> Lvl -> b) -> b -> LvlSet -> b
foldl f b s = go s b where
  go :: LvlSet -> b -> b
  go s b = popSmallest s (\s i -> go s (f b i)) b
{-# inline foldl #-}

foldr :: forall b. (Lvl -> b -> b) -> b -> LvlSet -> b
foldr f b s = go s where
  go :: LvlSet -> b
  go s = popSmallest s (\s i -> f i $! go s) b
{-# inline foldr #-}
