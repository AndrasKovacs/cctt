
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
  , wkSub
  ) where

import GHC.Exts
import Data.Foldable
import Data.Word

import Common
import qualified Data.IntIntMap as IIM
import qualified Data.LvlSet as LS
-- import qualified Data.IntSet.Internal as IS
-- import qualified Data.IntSet as IS

----------------------------------------------------------------------------------------------------

maxIVar :: IVar
maxIVar = 63

{-
Interval expressions are 64 bits:

- I0 is 0, I1 is 1, any other value N represents IVar (n - 2)

Substitution:
  - DomSize (32 bits) + CodSize (32 bits) + IntIntMap

IVarSet:
  - 64 bit mask of 0-63 var range
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

idSub :: IVar -> Sub
idSub i = Sub (fromIntegral i) (fromIntegral i) mempty

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
lookupSub i (Sub d c m)
  | 0 <= i && i < fromIntegral c
     = IIM.lookup (\_ -> IVar i) (\i -> I (fromIntegral i)) (fromIntegral i) m
  | True = error $ "lookupSub " ++ show i ++ " " ++ show (Sub d c m)
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

validI :: IVar -> I -> I
validI d = \case
  IVar i -> if i < d then IVar i else error (show i ++ " " ++ show d)
  i      -> i

-- | Extend a sub with an expression. Domain doesn't change.
ext :: Sub -> I -> Sub
ext (Sub d c m) i =
  let vi = validI (fromIntegral d) i in
  Sub d (c + 1) (IIM.insert (fromIntegral c) (fromIntegral (unI vi)) m)

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
mapSub domf f s@(Sub d c m) =
  Sub (fromIntegral (domf (fromIntegral d))) c
      (foldlSub
         (\x acc i -> case f x i of
             i' | IVar x == i' -> acc
                | True         -> IIM.insert (fromIntegral x) (fromIntegral (unI i')) acc)
         mempty
         s)
{-# inline mapSub #-}

-- substitution composition
instance SubAction Sub where
  sub f = mapSub (\_ -> dom ?sub) (\_ i -> sub i) f
  {-# noinline sub #-}

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

-- Weaken a sub to the current environment.
wkSub :: NCofArg => Sub -> Sub
wkSub s = setDom (dom ?cof) s
{-# inline wkSub #-}
