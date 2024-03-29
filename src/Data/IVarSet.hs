
-- | Sets of IVars. 64-bit, so 0-63 can be stored.

module Data.IVarSet where

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

intersect :: Set -> Set -> Set
intersect (Set w) (Set w') = Set (w .&. w')
{-# inline intersect #-}

singleton :: IVar -> Set
singleton x = insert x mempty
{-# inline singleton #-}

-- | Insert an unforced I.
insert :: IVar -> Set -> Set
insert (IVar# x) (Set s) = Set (unsafeShiftL 1 (w2i x) .|. s)
{-# inline insert #-}

insertError :: a
insertError = error "RAN OUT OF INTERVAL VARIABLES"
{-# noinline insertError #-}

insertI :: I -> Set -> Set
insertI i s = matchIVar i
  (\i -> if i <= maxIVar then insert i s else insertError)
  s
{-# inline insertI #-}

null :: Set -> Bool
null (Set 0) = True
null _       = False
{-# inline null #-}

delete :: IVar -> Set -> Set
delete (IVar# x) (Set s) = Set (complement (unsafeShiftL 1 (w2i x)) .&. s)
{-# inline delete #-}

member :: IVar -> Set -> Bool
member (IVar# x) (Set s) = (unsafeShiftL 1 (w2i x) .&. s) /= 0
{-# inline member #-}

toList :: Set -> [IVar]
toList = Data.IVarSet.foldr (:) []

fromList :: [IVar] -> Set
fromList = foldl' (flip insert) mempty

popSmallest :: Set -> (Set -> IVar -> a) -> a -> a
popSmallest (Set s) success ~fail = case s of
  0 -> fail
  s -> let i = IVar# (ctz s) in success (delete i (Set s)) i
{-# inline popSmallest #-}

instance Show Set where
  show = show . Data.IVarSet.toList

foldl :: forall b. (b -> IVar -> b) -> b -> Set -> b
foldl f b s = go s b where
  go :: Set -> b -> b
  go s b = popSmallest s (\s i -> go s (f b i)) b
{-# inline foldl #-}

foldr :: forall b. (IVar -> b -> b) -> b -> Set -> b
foldr f b s = go s where
  go :: Set -> b
  go s = popSmallest s (\s i -> f i $! go s) b
{-# inline foldr #-}

foldrAccum :: forall acc r. (IVar -> (acc -> r) -> acc -> r) -> acc -> r -> Set -> r
foldrAccum f acc r s = go s acc where
  go :: Set -> acc -> r
  go s acc = popSmallest s (\s i -> f i (go s) acc) r
{-# inline foldrAccum #-}

instance SubAction Set where
  sub is =
    snd $ Data.IVarSet.foldl
      (\(!sub, !acc) i ->
         sub // matchIVar (lookupSub i sub) (\i -> insert i acc) acc)
      (?sub :: Sub, mempty)
      is
  {-# noinline sub #-}
