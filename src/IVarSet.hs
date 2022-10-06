
module IVarSet where

import Data.Bits
import qualified LvlSet as LS

import Common

newtype IVarSet = IVarSet LS.LvlSet
  deriving (Eq, Bits, Semigroup, Monoid, Show) via LS.LvlSet

insert :: IVar -> IVarSet -> IVarSet
insert = coerce LS.insert
{-# inline insert #-}

delete :: IVar -> IVarSet -> IVarSet
delete = coerce LS.delete
{-# inline delete #-}

member :: IVar -> IVarSet -> Bool
member = coerce LS.member
{-# inline member #-}

toList :: IVarSet -> [IVar]
toList = coerce LS.toList
{-# inline toList #-}

fromList :: [IVar] -> IVarSet
fromList = coerce LS.fromList
{-# inline fromList #-}

popSmallest :: IVarSet -> (IVarSet -> IVar -> a) -> a -> a
popSmallest is f ~a = LS.popSmallest (coerce is) (coerce f) a
{-# inline popSmallest #-}

foldl :: forall b. (b -> IVar -> b) -> b -> IVarSet -> b
foldl f b is = LS.foldl (coerce f) b (coerce is)
{-# inline foldl #-}

foldr :: forall b. (IVar -> b -> b) -> b -> IVarSet -> b
foldr f b is = LS.foldr (coerce f) b (coerce is)
{-# inline foldr #-}
