
module LvlMap where

import qualified Data.IntMap.Strict as IM
import Common

newtype LvlMap a = LvlMap {unLvlMap :: IM.IntMap a}
  deriving (Eq, Show, Semigroup, Monoid) via IM.IntMap a

infixl 9 !
(!) :: LvlMap a -> Lvl -> a
(!) m x = coerce m IM.! fromIntegral x; {-# inline (!) #-}

lookup :: Lvl -> LvlMap a -> Maybe a
lookup x m = IM.lookup (fromIntegral x) (coerce m); {-# inline lookup #-}

insert :: Lvl -> a -> LvlMap a -> LvlMap a
insert x a m = coerce (IM.insert (fromIntegral x) a (coerce m)); {-# inline insert #-}

delete :: Lvl -> LvlMap a -> LvlMap a
delete x m = LvlMap (IM.delete (fromIntegral x) (unLvlMap m)); {-# inline delete #-}

update :: (a -> Maybe a) -> Lvl -> LvlMap a -> LvlMap a
update f x m = coerce (IM.update f (fromIntegral x) (coerce m)); {-# inline update #-}
