
{-# language UnboxedTuples #-}
{-# options_ghc -Wno-unused-top-binds #-}

module Interval (
    maxIVar
  , I
  , IVarSet
  , NCof
  , NCofArg
  , Sub
  , SubAction(..)
  , SubArg
  , cod
  , deleteIS
  , doSub
  , dom
  , emptySub
  , ext
  , foldrSub
  , idSub
  , insertI
  , insertIF
  , insertIVarF
  , isUnblocked
  , isUnblockedS
  , liftSub
  , mapCod
  , mapDom
  , mapSub
  , matchIVar
  , matchIVarF
  , pattern I0
  , pattern I1
  , pattern IVar
  , pushSub
  , setCod
  , setDom
  , setDomCod
  ) where

import GHC.Exts
import Data.Foldable
import Data.Word

import Common
import qualified Data.IntIntMap as IIM
-- import qualified Data.IntSet as IS
-- import qualified Data.IntSet.Internal as IS
import qualified Data.LvlSet as LS

--------------------------------------------------------------------------------

-- TODO for general arbitrary precision representations:
--   - LvlSet is an unboxed sum of a 64 bit mask and a 32-bit-keyed custom IntSet
--   - Sub is a 32-bit keyed custom IntMap

----------------------------------------------------------------------------------------------------


maxIVar :: IVar
maxIVar = 63

{-

Interval expressions are 64 bits:

- I0 is 0, I1 is 1, any other value N represents IVar (n - 2)

We have small and big interval substitutions.

Small:
  - domain & codomain sizes are at most 12
  - storage: 64 bits, 16 nibbles
    - 0    : always 0
    - 1    : always 1
    - 2-14 : stores 4-bit interval expression
  - When indexing into a small Sub, we add 2 to an IVar, to skip over the 0-1 nibbles
  - This implies that sub-ing and I with a SmallSub is just nibble lookup.

Big:
  - DomSize (32 bits) + CodSize (32 bits) + IntIntMap
-}

-- data I = I0 | I1 | IVar IVar
newtype I = I {unI :: Word}
  deriving Eq

unpackI# :: I -> (# (# #) | (# #) | Word# #)
unpackI# (I (W# x)) = case x of
  0## -> (# (# #) |       |                    #)  -- I0
  1## -> (#       | (# #) |                    #)  -- I1
  x   -> (#       |       | x `minusWord#` 2## #)  -- IVar
{-# inline unpackI# #-}

pattern I0 :: I
pattern I0 <- (unpackI# -> (# (# #) | | #)) where I0 = I 0

pattern I1 :: I
pattern I1 <- (unpackI# -> (# | (# #) | #)) where I1 = I 1

pattern IVar :: IVar -> I
pattern IVar x <- (unpackI# -> (# | | (W# -> (IVar# -> x)) #)) where
  IVar (IVar# x) = I (x + 2)
{-# complete I0, I1, IVar #-}

matchIVar :: NCofArg => I -> (IVar -> a) -> a -> a
matchIVar (doSub ?cof -> I x) f ~a | x >= 2 = f (IVar# (x - 2))
                                   | True   = a
{-# inline matchIVar #-}

matchIVarF :: I -> (IVar -> a) -> a -> a
matchIVarF (I x) f ~a | x >= 2 = f (IVar# (x - 2))
                      | True   = a
{-# inline matchIVarF #-}

instance Show I where
  showsPrec _ I0       acc = 'I':'0':acc
  showsPrec _ I1       acc = 'I':'1':acc
  showsPrec d (IVar x) acc = showParen (d > 10) (("IVar " ++).showsPrec 11 x) acc

----------------------------------------------------------------------------------------------------

newtype IVarSet = IVarSet LS.LvlSet
  deriving (Eq, Bits, Semigroup, Monoid, Show) via LS.LvlSet

emptyIS :: IVarSet -> Bool
emptyIS = coerce LS.null
{-# inline emptyIS #-}

-- | Insert a forced I.
insertIF :: I -> IVarSet -> IVarSet
insertIF i is = matchIVarF i (\x -> coerce LS.insert x is) is
{-# inline insertIF #-}

-- | Insert a forced variable.
insertIVarF :: IVar -> IVarSet -> IVarSet
insertIVarF i is = coerce LS.insert i is
{-# inline insertIVarF #-}

insertI :: NCofArg => I -> IVarSet -> IVarSet
insertI i is = matchIVar i (\x -> insertIVarF x is) is
{-# inline insertI #-}

deleteIS :: IVar -> IVarSet -> IVarSet
deleteIS = coerce LS.delete
{-# inline deleteIS #-}

memberIS :: IVar -> IVarSet -> Bool
memberIS = coerce LS.member
{-# inline memberIS #-}

toListIS :: IVarSet -> [IVar]
toListIS = coerce LS.toList
{-# inline toListIS #-}

fromListIS :: [IVar] -> IVarSet
fromListIS = coerce LS.fromList
{-# inline fromListIS #-}

popSmallestIS :: IVarSet -> (IVarSet -> IVar -> a) -> a -> a
popSmallestIS is f ~a = LS.popSmallest (coerce is) (coerce f) a
{-# inline popSmallestIS #-}

foldlIS :: forall b. (b -> IVar -> b) -> b -> IVarSet -> b
foldlIS f b is = LS.foldl (coerce f) b (coerce is)
{-# inline foldlIS #-}

foldrIS :: forall b. (IVar -> b -> b) -> b -> IVarSet -> b
foldrIS f b is = LS.foldr (coerce f) b (coerce is)
{-# inline foldrIS #-}

foldrAccumIS :: forall acc r. (IVar -> (acc -> r) -> acc -> r)
                -> acc -> r -> IVarSet -> r
foldrAccumIS f acc r s = LS.foldrAccum (\x hyp acc -> f (coerce x) hyp acc) acc r (coerce s)
{-# inline foldrAccumIS #-}

--------------------------------------------------------------------------------

-- newtype IVarSet = IVarSet IS.IntSet
--   deriving (Eq, Semigroup, Monoid, Show) via IS.IntSet

-- emptyIS :: IVarSet -> Bool
-- emptyIS = coerce IS.null
-- {-# inline emptyIS #-}

-- -- | Insert a forced I.
-- insertIF :: I -> IVarSet -> IVarSet
-- insertIF i is = matchIVarF i (\x -> coerce (IS.insert (fromIntegral x) (coerce is))) is
-- {-# inline insertIF #-}

-- -- | Insert a forced variable.
-- insertIVarF :: IVar -> IVarSet -> IVarSet
-- insertIVarF i is = coerce (IS.insert (fromIntegral i) (coerce is))
-- {-# inline insertIVarF #-}

-- insertI :: NCofArg => I -> IVarSet -> IVarSet
-- insertI i is = matchIVar i (\x -> insertIVarF x is) is
-- {-# inline insertI #-}

-- deleteIS :: IVar -> IVarSet -> IVarSet
-- deleteIS i is = coerce (IS.delete (fromIntegral i) (coerce is))
-- {-# inline deleteIS #-}

-- memberIS :: IVar -> IVarSet -> Bool
-- memberIS i is = IS.member (fromIntegral i) (coerce is)
-- {-# inline memberIS #-}

-- toListIS :: IVarSet -> [IVar]
-- toListIS is = IS.foldr' (\i is -> fromIntegral i : is) [] (coerce is)
-- {-# inline toListIS #-}

-- fromListIS :: [IVar] -> IVarSet
-- fromListIS is = coerce (IS.fromList (map fromIntegral is))
-- {-# inline fromListIS #-}

-- foldlIS :: forall b. (b -> IVar -> b) -> b -> IVarSet -> b
-- foldlIS f b is = IS.foldl' (\b i -> f b (fromIntegral i)) b (coerce is)
-- {-# inline foldlIS #-}

-- foldrIS :: forall b. (IVar -> b -> b) -> b -> IVarSet -> b
-- foldrIS f b is = IS.foldr (\i ~b -> f (fromIntegral i) b) b (coerce is)
-- {-# inline foldrIS #-}

----------------------------------------------------------------------------------------------------

{-|
Small interval substitutions are nibble (4-bit) sequences stored in a 64-bit word.

  - 0    : mapped to 0
  - 1    : mapped to 1
  - 2-13 : mapped to I expressions
  - 14   : mapped to the domain size
  - 15   : mapped to the codomain size
-}

data Sub = Sub Word32 Word32 IIM.IntIntMap  -- dom, cod, map
  deriving Eq

type SubArg = (?sub :: Sub)  -- ImplicitParams


{-|
Normalized cofibrations are also represented as interval substitutions. Here,
every ivar is mapped to the *least* (as a De Bruijn level) representative of
its equivalence class.
INVARIANT: the dom and cod fields of an NCof must be identical.
-}
type NCof = Sub
type NCofArg = (?cof :: NCof)

emptySub :: IVar -> Sub
emptySub i = Sub (fromIntegral i) 0 mempty
{-# inline emptySub #-}

-- idSubCacheLimit :: IVar
-- idSubCacheLimit = 100

idSub :: IVar -> Sub
idSub i = Sub (fromIntegral i) (fromIntegral i) mempty

-- -- Precomputed identity subs up to some limit
-- idSubs :: IM.IntMap Sub
-- idSubs = go 0 mempty mempty where
--   go :: IVar -> IIM.IntIntMap -> IM.IntMap Sub -> IM.IntMap Sub
--   go i s acc | i > idSubCacheLimit = acc
--   go i s acc = let s' = (IIM.insert (fromIntegral i) (fromIntegral (unI (IVar (fromIntegral i)))) s)
--                in go (i + 1) s' (IM.insert (fromIntegral i) (Sub (fromIntegral i) (fromIntegral i) s) acc)

-- idSub :: IVar -> Sub
-- idSub i | i < idSubCacheLimit = idSubs IM.! fromIntegral i
--         | otherwise           = undefined

-- -- direct recomp
-- idSub :: IVar -> Sub
-- idSub i = Sub (fromIntegral i) (fromIntegral i) (go 0 i mempty) where
--   go :: IVar -> IVar -> IIM.IntIntMap -> IIM.IntIntMap
--   go x i acc | x == i = acc
--   go x i acc = go (x + 1) i (IIM.insert (fromIntegral x) (fromIntegral (unI (IVar (fromIntegral x)))) acc)
-- {-# inline idSub #-}

cod :: Sub -> IVar
cod (Sub _ c _) = fromIntegral c
{-# inline cod #-}

setCod :: IVar -> Sub -> Sub
setCod i (Sub d _ m) = Sub d (fromIntegral i) m
{-# inline setCod #-}

dom :: Sub -> IVar
dom (Sub d _ _) = fromIntegral d
{-# inline dom #-}

setDom :: IVar -> Sub -> Sub
setDom i (Sub _ c m) = Sub (fromIntegral i) c m
{-# inline setDom #-}

setDomCod :: IVar -> IVar -> Sub -> Sub
setDomCod d c (Sub _ _ m) = Sub (fromIntegral d) (fromIntegral c) m
{-# inline setDomCod #-}

lookupSub :: IVar -> Sub -> I
lookupSub i (Sub _ _ m) = IIM.lookup (\_ -> IVar i) (\i -> I (fromIntegral i)) (fromIntegral i) m
{-# inline lookupSub #-}

-- | Strict right fold over all (index, I) mappings in a substitution.
foldrSub :: forall b. (IVar -> I -> b -> b) -> b -> Sub -> b
foldrSub f b (Sub _ c m) = go 0 (fromIntegral c) where
  go :: Int -> Int -> b
  go i c | i < c = IIM.lookup
                     (\_ -> f (fromIntegral i) (IVar (fromIntegral i)) (go (i + 1) c))
                     (\x -> f (fromIntegral i) (I (fromIntegral x)) (go (i + 1) c)) i m
         | True  = b
{-# inline foldrSub #-}

foldlSub :: forall b. (IVar -> b -> I -> b) -> b -> Sub -> b
foldlSub f b (Sub _ c m) = go 0 (fromIntegral c) b where
  go :: Int -> Int -> b -> b
  go i c b | i < c = IIM.lookup
                       (\_ -> go (i + 1) c (f (fromIntegral i) b (IVar (fromIntegral i))))
                       (\x -> go (i + 1) c (f (fromIntegral i) b (I (fromIntegral x)))) i m
           | True  = b
{-# inline foldlSub #-}


-- | Extend a sub with an expression. Domain doesn't change.
ext :: Sub -> I -> Sub
ext (Sub d c m) i = Sub d (c + 1) (IIM.insert (fromIntegral c) (fromIntegral (unI i)) m)

liftSub :: Sub -> Sub
liftSub (Sub d c m) =
  Sub (d + 1) (c + 1)
      (IIM.insert (fromIntegral c) (fromIntegral (unI (IVar (fromIntegral d)))) m)
{-# inline liftSub #-}

subToList :: Sub -> [I]
subToList = foldrSub (\_ i is -> i:is) []

subFromList :: [I] -> Sub
subFromList is =
  let dom = case [x | IVar x <- is] of [] -> 0; is -> maximum is + 1
  in foldl' ext (emptySub dom) is

instance Show Sub where
  show s = let d = dom s; c = cod s; s' = subToList s in
           show (d, c, s')

mapDom :: (IVar -> IVar) -> Sub -> Sub
mapDom f s = setDom (f (dom s)) s
{-# inline mapDom #-}

mapCod :: (IVar -> IVar) -> Sub -> Sub
mapCod f s = setCod (f (cod s)) s
{-# inline mapCod #-}

class SubAction a where
  sub :: SubArg => a -> a

doSub :: SubAction a => Sub -> a -> a
doSub s a = let ?sub = s in sub a
{-# inline doSub #-}

instance SubAction I where
  sub (IVar i) = lookupSub i ?sub
  sub i        = i
  {-# inline sub #-}

mapSub :: (IVar -> IVar) -> (IVar -> I -> I) -> Sub -> Sub
mapSub domf f (Sub d c m) =
  Sub (fromIntegral (domf (fromIntegral d)))
      c (IIM.mapWithKey (\k i -> fromIntegral (unI (f (fromIntegral k) (I (fromIntegral i))))) m)
{-# inline mapSub #-}

-- substitution composition
instance SubAction Sub where
  sub f = mapSub (\_ -> dom ?sub) (\_ i -> sub i) f
  {-# noinline sub #-}

-- goIsUnblocked :: NCofArg => IVarSet -> IVarSet -> Bool
-- goIsUnblocked is varset = popSmallestIS is
--   (\is x -> matchIVar (lookupSub x ?cof)
--      (\x -> memberIS x varset || goIsUnblocked is (insertIVarF x varset))
--      True)
--   False

goIsUnblocked :: NCofArg => IVarSet -> IVarSet -> Bool
goIsUnblocked is varset =
  foldrAccumIS
    (\x hyp varset -> matchIVar (lookupSub x ?cof)
       (\x -> memberIS x varset || hyp (insertIVarF x varset))
       True)
    varset
    False
    is

-- A set of blocking ivars is still blocked under a cofibration
-- if all vars in the set are represented by distinct vars.
isUnblocked :: NCofArg => IVarSet -> Bool
isUnblocked is | emptyIS is = False
isUnblocked is = goIsUnblocked is mempty
{-# inline isUnblocked #-}

goIsUnblockedS :: SubArg => NCofArg => IVarSet -> IVarSet -> Bool
goIsUnblockedS is varset =
  foldrAccumIS
    (\x hyp varset -> matchIVar (lookupSub x ?sub)
      (\x -> matchIVar (lookupSub x ?cof)
        (\x -> memberIS x varset || hyp (insertIVarF x varset))
        True)
      True)
    varset
    False
    is

-- goIsUnblockedS :: SubArg => NCofArg => IVarSet -> IVarSet -> Bool
-- goIsUnblockedS is varset = popSmallestIS is
--     (\is x -> matchIVar (lookupSub x ?sub)
--       (\x -> matchIVar (lookupSub x ?cof)
--         (\x -> memberIS x varset || goIsUnblockedS is (insertIVarF x varset))
--         True)
--       True)
--     False

isUnblockedS :: SubArg => NCofArg => IVarSet -> Bool
isUnblockedS is | emptyIS is = False
isUnblockedS is = goIsUnblockedS is mempty
{-# inline isUnblockedS #-}

instance SubAction IVarSet where
  sub is = foldlIS
    (\acc i -> insertIF (lookupSub i ?sub) acc)
    mempty is
  {-# noinline sub #-}

pushSub :: Sub -> Sub -> Sub
pushSub s s' = foldlSub (\_ -> ext) s s'
