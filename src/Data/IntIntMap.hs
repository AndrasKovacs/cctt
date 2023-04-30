
module Data.IntIntMap (
    IntIntMap
  , Data.IntIntMap.null
  , singleton
  , member
  , insert
  , delete
  , Data.IntIntMap.lookup
  , union
  , elems
  , keys
  , assocs
  , fromList
  , mapWithKey
  , foldlWithKey'
  , foldrWithKey'
  , (!)
  ) where

import Common
import Data.Foldable (foldl')

type Nat    = Word
type Prefix = Int
type Mask   = Int

-- The highestBitMask implementation is based on
-- http://graphics.stanford.edu/~seander/bithacks.html#RoundUpPowerOf2
-- which has been put in the public domain.

-- | Return a word where only the highest bit is set.
highestBitMask :: Word -> Word
highestBitMask w = shiftLL 1 (wordSize - 1 - countLeadingZeros w)
{-# inline highestBitMask #-}

-- Right and left logical shifts.
shiftLL :: Word -> Int -> Word

shiftLL = unsafeShiftL; {-# inline shiftLL #-}

wordSize :: Int
wordSize = finiteBitSize (0 :: Word)
{-# inline wordSize #-}

natFromInt :: Int -> Nat
natFromInt = fromIntegral
{-# inline natFromInt #-}

intFromNat :: Nat -> Int
intFromNat = fromIntegral
{-# inline intFromNat #-}

zero :: Int -> Mask -> Bool
zero i m
  = (natFromInt i) .&. (natFromInt m) == 0
{-# inline zero #-}

-- | The prefix of key @i@ up to (but not including) the switching
-- bit @m@.
mask :: Int -> Mask -> Prefix
mask i m
  = maskW (natFromInt i) (natFromInt m)
{-# inline mask #-}



-- | Does the key @i@ differ from the prefix @p@ before getting to
-- the switching bit @m@?
nomatch i p m
  = (mask i m) /= p
{-# inline nomatch #-}

-- | The prefix of key @i@ up to (but not including) the switching
-- bit @m@.
maskW :: Nat -> Nat -> Prefix
maskW i m
  = intFromNat (i .&. ((-m) `xor` m))
{-# inline maskW #-}

-- | The first switching bit where the two prefixes disagree.
branchMask :: Prefix -> Prefix -> Mask
branchMask p1 p2
  = intFromNat (highestBitMask (natFromInt p1 `xor` natFromInt p2))
{-# inline branchMask #-}

link :: Prefix -> IntIntMap -> Prefix -> IntIntMap -> IntIntMap
link p1 t1 p2 t2 = linkWithMask (branchMask p1 p2) p1 t1 {-p2-} t2
{-# inline link #-}

-- `linkWithMask` is useful when the `branchMask` has already been computed
linkWithMask :: Mask -> Prefix -> IntIntMap -> IntIntMap -> IntIntMap
linkWithMask m p1 t1 {-p2-} t2
  | zero p1 m = Bin p m t1 t2
  | otherwise = Bin p m t2 t1
  where
    p = mask p1 m
{-# inline linkWithMask #-}

-- | Does the left switching bit specify a shorter prefix?
shorter :: Mask -> Mask -> Bool
shorter m1 m2
  = (natFromInt m1) > (natFromInt m2)
{-# INLINE shorter #-}


--------------------------------------------------------------------------------

data IntIntMap
  = Bin Prefix Mask IntIntMap IntIntMap
  | Tip Int Int
  | Nil

null :: IntIntMap -> Bool
null Nil = True
null _   = False
{-# INLINE null #-}

lookup :: (Int -> a) -> (Int -> a) -> Int -> IntIntMap -> a
lookup nothing just !k = go k
  where
    go k (Bin _p m l r) | zero k m  = go k l
                        | otherwise = go k r
    go k (Tip kx x) | k == kx   = just x
                    | otherwise = nothing k
    go k Nil = nothing k
{-# inline lookup #-}

infixl 9 !
(!) :: IntIntMap -> Int -> Int
(!) m k = Data.IntIntMap.lookup not_found id k m where
  not_found k = error ("IntMap.!: key " ++ show k ++ " is not an element of the map")

member :: Int -> IntIntMap -> Bool
member k m = Data.IntIntMap.lookup (\_ -> False) (\_ -> True) k m

instance Semigroup IntIntMap where
  (<>) = union; {-# inline (<>) #-}

instance Monoid IntIntMap where
  mempty = Nil; {-# inline mempty #-}

instance Show IntIntMap where
  show = show . assocs

singleton :: Int -> Int -> IntIntMap
singleton = Tip; {-# inline singleton #-}

insert :: Int -> Int -> IntIntMap -> IntIntMap
insert !k x t@(Bin p m l r)
  | nomatch k p m = link k (Tip k x) p t
  | zero k m      = Bin p m (insert k x l) r
  | otherwise     = Bin p m l (insert k x r)
insert k x t@(Tip ky _)
  | k==ky         = Tip k x
  | otherwise     = link k (Tip k x) ky t
insert k x Nil = Tip k x

-- binCheckLeft only checks that the left subtree is non-empty
binCheckLeft :: Prefix -> Mask -> IntIntMap -> IntIntMap -> IntIntMap
binCheckLeft _ _ Nil r = r
binCheckLeft p m l r   = Bin p m l r
{-# inline binCheckLeft #-}

-- binCheckRight only checks that the right subtree is non-empty
binCheckRight :: Prefix -> Mask -> IntIntMap -> IntIntMap -> IntIntMap
binCheckRight _ _ l Nil = l
binCheckRight p m l r   = Bin p m l r
{-# inline binCheckRight #-}

delete :: Int -> IntIntMap -> IntIntMap
delete !k t@(Bin p m l r)
  | nomatch k p m = t
  | zero k m      = binCheckLeft p m (delete k l) r
  | otherwise     = binCheckRight p m l (delete k r)
delete k t@(Tip ky _)
  | k == ky       = Nil
  | otherwise     = t
delete _k Nil = Nil

union :: IntIntMap -> IntIntMap -> IntIntMap
union m1 m2 = mergeWithKey' Bin const id id m1 m2


-- Slightly more general version of mergeWithKey. It differs in the following:
--
-- * the combining function operates on maps instead of keys and values. The
--   reason is to enable sharing in union, difference and intersection.
--
-- * mergeWithKey' is given an equivalent of bin. The reason is that in union*,
--   Bin constructor can be used, because we know both subtrees are nonempty.

mergeWithKey' :: (Prefix -> Mask -> IntIntMap -> IntIntMap -> IntIntMap)
              -> (IntIntMap -> IntIntMap -> IntIntMap) -> (IntIntMap -> IntIntMap) -> (IntIntMap -> IntIntMap)
              -> IntIntMap -> IntIntMap -> IntIntMap
mergeWithKey' bin' f g1 g2 = go
  where
    go t1@(Bin p1 m1 l1 r1) t2@(Bin p2 m2 l2 r2)
      | shorter m1 m2  = merge1
      | shorter m2 m1  = merge2
      | p1 == p2       = bin' p1 m1 (go l1 l2) (go r1 r2)
      | otherwise      = maybe_link p1 (g1 t1) p2 (g2 t2)
      where
        merge1 | nomatch p2 p1 m1  = maybe_link p1 (g1 t1) p2 (g2 t2)
               | zero p2 m1        = bin' p1 m1 (go l1 t2) (g1 r1)
               | otherwise         = bin' p1 m1 (g1 l1) (go r1 t2)
        merge2 | nomatch p1 p2 m2  = maybe_link p1 (g1 t1) p2 (g2 t2)
               | zero p1 m2        = bin' p2 m2 (go t1 l2) (g2 r2)
               | otherwise         = bin' p2 m2 (g2 l2) (go t1 r2)

    go t1'@(Bin _ _ _ _) t2'@(Tip k2' _) = merge0 t2' k2' t1'
      where
        merge0 t2 k2 t1@(Bin p1 m1 l1 r1)
          | nomatch k2 p1 m1 = maybe_link p1 (g1 t1) k2 (g2 t2)
          | zero k2 m1 = bin' p1 m1 (merge0 t2 k2 l1) (g1 r1)
          | otherwise  = bin' p1 m1 (g1 l1) (merge0 t2 k2 r1)
        merge0 t2 k2 t1@(Tip k1 _)
          | k1 == k2 = f t1 t2
          | otherwise = maybe_link k1 (g1 t1) k2 (g2 t2)
        merge0 t2 _  Nil = g2 t2

    go t1@(Bin _ _ _ _) Nil = g1 t1

    go t1'@(Tip k1' _) t2' = merge0 t1' k1' t2'
      where
        merge0 t1 k1 t2@(Bin p2 m2 l2 r2)
          | nomatch k1 p2 m2 = maybe_link k1 (g1 t1) p2 (g2 t2)
          | zero k1 m2 = bin' p2 m2 (merge0 t1 k1 l2) (g2 r2)
          | otherwise  = bin' p2 m2 (g2 l2) (merge0 t1 k1 r2)
        merge0 t1 k1 t2@(Tip k2 _)
          | k1 == k2 = f t1 t2
          | otherwise = maybe_link k1 (g1 t1) k2 (g2 t2)
        merge0 t1 _  Nil = g1 t1

    go Nil t2 = g2 t2

    maybe_link :: Int -> IntIntMap -> Int -> IntIntMap -> IntIntMap
    maybe_link _ Nil _ t2 = t2
    maybe_link _ t1 _ Nil = t1
    maybe_link p1 t1 p2 t2 = link p1 t1 p2 t2
    {-# INLINE maybe_link #-}
{-# INLINE mergeWithKey' #-}

mapWithKey :: (Int -> Int -> Int) -> IntIntMap -> IntIntMap
mapWithKey f = go where
  go t = case t of
    Bin p m l r -> Bin p m (go l) (go r)
    Tip k x     -> Tip k (f k x)
    Nil         -> Nil
{-# inline mapWithKey #-}

instance Eq IntIntMap where
  t1 == t2  = equal t1 t2; {-# inline (==) #-}
  t1 /= t2  = nequal t1 t2; {-# inline (/=) #-}

equal :: IntIntMap -> IntIntMap -> Bool
equal (Bin p1 m1 l1 r1) (Bin p2 m2 l2 r2)
  = (m1 == m2) && (p1 == p2) && (equal l1 l2) && (equal r1 r2)
equal (Tip kx x) (Tip ky y)
  = (kx == ky) && (x==y)
equal Nil Nil = True
equal _   _   = False

nequal :: IntIntMap -> IntIntMap -> Bool
nequal (Bin p1 m1 l1 r1) (Bin p2 m2 l2 r2)
  = (m1 /= m2) || (p1 /= p2) || (nequal l1 l2) || (nequal r1 r2)
nequal (Tip kx x) (Tip ky y)
  = (kx /= ky) || (x/=y)
nequal Nil Nil = False
nequal _   _   = True

foldlWithKey' :: (a -> Int -> Int -> a) -> a -> IntIntMap -> a
foldlWithKey' f z = \t ->      -- Use lambda t to be inlinable with two arguments only.
  case t of
    Bin _ m l r
      | m < 0     -> go (go z r) l -- put negative numbers before
      | otherwise -> go (go z l) r
    _ -> go z t
  where
    go !z' Nil          = z'
    go z' (Tip kx x)    = f z' kx x
    go z' (Bin _ _ l r) = go (go z' l) r
{-# INLINE foldlWithKey' #-}

foldrWithKey' :: (Int -> Int -> b -> b) -> b -> IntIntMap -> b
foldrWithKey' f z = \t ->      -- Use lambda t to be inlinable with two arguments only.
  case t of
    Bin _ m l r
      | m < 0     -> go (go z l) r -- put negative numbers before
      | otherwise -> go (go z r) l
    _ -> go z t
  where
    go !z' Nil          = z'
    go z' (Tip kx x)    = f kx x z'
    go z' (Bin _ _ l r) = go (go z' r) l
{-# INLINE foldrWithKey' #-}

elems :: IntIntMap -> [Int]
elems = foldrWithKey' (\_ n ns -> n : ns) []

keys  :: IntIntMap -> [Int]
keys = foldrWithKey' (\k _ ks -> k : ks) []

assocs :: IntIntMap -> [(Int, Int)]
assocs = foldrWithKey' (\k n ns -> (k, n):ns) []

fromList :: [(Int, Int)] -> IntIntMap
fromList = foldl' (\acc (k, n) -> insert k n acc) mempty
