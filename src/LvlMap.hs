
module LvlMap where

import qualified Data.IntMap.Strict as IM
import Common

newtype Map a = Map {unMap :: IM.IntMap a}
  deriving (Eq, Show, Semigroup, Monoid) via IM.IntMap a

infixl 9 !
(!) :: Map a -> Lvl -> a
(!) m x = coerce m IM.! fromIntegral x; {-# inline (!) #-}

lookup :: Lvl -> Map a -> Maybe a
lookup x m = IM.lookup (fromIntegral x) (coerce m); {-# inline lookup #-}

insert :: Lvl -> a -> Map a -> Map a
insert x a m = coerce (IM.insert (fromIntegral x) a (coerce m)); {-# inline insert #-}

delete :: Lvl -> Map a -> Map a
delete x m = Map (IM.delete (fromIntegral x) (unMap m)); {-# inline delete #-}

update :: (a -> Maybe a) -> Lvl -> Map a -> Map a
update f x m = coerce (IM.update f (fromIntegral x) (coerce m)); {-# inline update #-}

adjust :: (a -> a) -> Lvl -> Map a -> Map a
adjust f x m = coerce (IM.adjust f (fromIntegral x) (coerce m)); {-# inline adjust #-}

elems :: Map a -> [a]
elems x = IM.elems (coerce x); {-# inline elems #-}

foldrWithKey' :: (Lvl -> a -> b -> b) -> b -> Map a -> b
foldrWithKey' f b as = IM.foldrWithKey' (\l a b -> f (fromIntegral l) a b) b (unMap as)
{-# inline foldrWithKey' #-}
