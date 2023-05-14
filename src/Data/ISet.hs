
-- | Sets of interval expressions. 64-bit, so I0, I1, and IVar-s at most 61 can be stored.

module Data.ISet where

import Data.Foldable
import Common
import Cubical.Interval
import Cubical.Substitution

newtype Set = Set Word deriving (Eq, Bits) via Word

instance Semigroup Set where
  (<>) = (.|.)
  {-# inline (<>) #-}

instance Monoid Set where
  mempty = Set 0
  {-# inline mempty #-}

singleton :: I -> Set
singleton x = insert x mempty
{-# inline singleton #-}

delete01 :: Set -> Set
delete01 (Set w) = Set (w .&. 18446744073709551612)
{-# inline delete01 #-}

-- | Insert an unforced I.
insert :: I -> Set -> Set
insert (I x) (Set s) = Set (unsafeShiftL 1 (w2i x) .|. s)
{-# inline insert #-}

insertIVar :: IVar -> Set -> Set
insertIVar i s = insert (IVar i) s
{-# inline insertIVar #-}

null :: Set -> Bool
null (Set 0) = True
null _       = False
{-# inline null #-}

delete :: I -> Set -> Set
delete (I x) (Set s) = Set (complement (unsafeShiftL 1 (w2i x)) .&. s)
{-# inline delete #-}

deleteIVar :: IVar -> Set -> Set
deleteIVar i s = delete (IVar i) s
{-# inline deleteIVar #-}

member :: I -> Set -> Bool
member (I x) (Set s) = (unsafeShiftL 1 (w2i x) .&. s) /= 0
{-# inline member #-}

memberIVar :: IVar -> Set -> Bool
memberIVar i s = member (IVar i) s
{-# inline memberIVar #-}

toList :: Set -> [I]
toList = Data.ISet.foldr (:) []

fromList :: [I] -> Set
fromList = foldl' (flip insert) mempty

popSmallest :: Set -> (Set -> I -> a) -> a -> a
popSmallest (Set s) success ~fail = case s of
  0 -> fail
  s -> let i = I (ctz s) in success (delete i (Set s)) i
{-# inline popSmallest #-}

instance Show Set where
  show = show . Data.ISet.toList

foldl :: forall b. (b -> I -> b) -> b -> Set -> b
foldl f b s = go s b where
  go :: Set -> b -> b
  go s b = popSmallest s (\s i -> go s (f b i)) b
{-# inline foldl #-}

foldr :: forall b. (I -> b -> b) -> b -> Set -> b
foldr f b s = go s where
  go :: Set -> b
  go s = popSmallest s (\s i -> f i $! go s) b
{-# inline foldr #-}

foldrAccum :: forall acc r. (I -> (acc -> r) -> acc -> r) -> acc -> r -> Set -> r
foldrAccum f acc r s = go s acc where
  go :: Set -> acc -> r
  go s acc = popSmallest s (\s i -> f i (go s) acc) r
{-# inline foldrAccum #-}

instance SubAction Set where
  sub is =
    snd $ Data.ISet.foldl
      (\(!sub, !acc) i -> sub // insert (sub i) acc)
      (sub, mempty)
      is
  {-# noinline sub #-}
