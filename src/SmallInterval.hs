{-# language UnboxedTuples #-}

module SmallInterval where

import GHC.Exts
import Data.Bits
import Data.Foldable

import Common
import qualified Data.LvlSet as LS

--------------------------------------------------------------------------------

-- TODO for arbitrary precision:
--       - export explicit minimal interface
--       - represent I0 and I1 as maxBound and (maxBound - 1), adjust accordingly
--       - define and test parallel Interval module using *only* IntIntMap subs.
--       - have 3 modules: one with smallSub, one with Big, one with the coproduct of these

----------------------------------------------------------------------------------------------------

maxIVar :: IVar
maxIVar = 11

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

TODO:
  - We'll need large IVarSet-s as well.
  - Current IVarSet-s work up to 63 so there's a bit more leeway.

QUESTION:
  - should BigSub-s be sparse? I.e. implicitly mapping every var that's not in the map domain
    to itself.
-}

-- data I = I0 | I1 | IVar IVar
newtype I = I Word
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

----------------------------------------------------------------------------------------------------

{-|
Small interval substitutions are nibble (4-bit) sequences stored in a 64-bit word.

  - 0    : mapped to 0
  - 1    : mapped to 1
  - 2-13 : mapped to I expressions
  - 14   : mapped to the domain size
  - 15   : mapped to the codomain size
-}

newtype Sub = Sub {unSub :: Word}
  deriving Eq via Word

type SubArg = (?sub :: Sub)  -- ImplicitParams

{-|
Normalized cofibrations are also represented as interval substitutions. Here,
every ivar is mapped to the *least* (as a De Bruijn level) representative of
its equivalence class.

INVARIANT: the dom and cod fields of an NCof must be identical.
-}
type NCof = Sub
type NCofArg = (?cof :: NCof)

nibblesToSub :: [Word] -> Sub
nibblesToSub ns = Sub (go 0 0 ns) where
  go shift acc []     = acc
  go shift acc (n:ns) = go (shift + 4) (unsafeShiftL n shift .|. acc) ns

subToNibbles :: Sub -> [Word]
subToNibbles (Sub s) = go (0 :: Int) s where
  go 16 _ = []
  go i  n = n .&. 15 : go (i + 1) (unsafeShiftR n 4)

emptySub# :: Word -> Word
emptySub# dom = unsafeShiftL dom 60 .|. 62129658859368976
{-# inline emptySub# #-}

emptySub :: IVar -> Sub
emptySub dom = Sub (emptySub# (coerce dom))
{-# inline emptySub #-}

idSub :: IVar -> Sub
idSub (IVar# x) = Sub (emptySub# x .|. unsafeShiftL x 56)
{-# inline idSub #-}

cod :: Sub -> IVar
cod (Sub n) = coerce (unsafeShiftR (unsafeShiftL n 4) 60)
{-# inline cod #-}

setCod :: IVar -> Sub -> Sub
setCod i (Sub n) = Sub (n .&. 17365880163140632575 .|. unsafeShiftL (coerce i) 56)
{-# inline setCod #-}

dom :: Sub -> IVar
dom (Sub n) = coerce (unsafeShiftR n 60)
{-# inline dom #-}

setDom :: IVar -> Sub -> Sub
setDom i (Sub n) = Sub (n .&. 1152921504606846975 .|. unsafeShiftL (coerce i) 60)
{-# inline setDom #-}

setDomCod :: IVar -> IVar -> Sub -> Sub
setDomCod d c (Sub n) = Sub (
  n .&. 72057594037927935 .|. unsafeShiftL (coerce d) 60 .|. unsafeShiftL (coerce c) 56)
{-# inline setDomCod #-}

lookupSub# :: Word -> Sub -> I
lookupSub# w (Sub s) = I (unsafeShiftR s (unsafeShiftL (w2i w) 2) .&. 15)
{-# inline lookupSub# #-}

lookupSub :: IVar -> Sub -> I
lookupSub (IVar# x) s = lookupSub# (x + 2) s
{-# inline lookupSub #-}

-- | Strict right fold over all (index, I) mappings in a substitution.
foldrSub :: forall b. (IVar -> I -> b -> b) -> b -> Sub -> b
foldrSub f b (Sub s) = go 0 (cod (Sub s)) (unsafeShiftR s 8) where
  go i l n | i < l = f i (I (n .&. 15)) $! go (i + 1) l (unsafeShiftR n 4)
  go i l n = b
{-# inline foldrSub #-}

foldlSub :: (IVar -> b -> I -> b) -> b -> Sub -> b
foldlSub f b (Sub s) = go 0 (cod (Sub s)) (unsafeShiftR s 8) b where
  go i l n b | i < l = go (i + 1) l (unsafeShiftR n 4) (f i b (I (n .&. 15)))
  go i l n b = b

-- | Extend a sub with an expression. Domain doesn't change.
ext :: Sub -> I -> Sub
ext (Sub s) i =
  let len   = cod (Sub s)
      shift = w2i (unsafeShiftL (coerce len) 2) + 8
  in setCod (len + 1)
            (Sub (s .&. complement (unsafeShiftL 15 shift)
                    .|. unsafeShiftL (coerce i) shift))
{-# inline ext #-}

liftSub :: Sub -> Sub
liftSub s = let d = dom s in setDom (d + 1) (ext s (IVar d))
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
  sub (I w) = lookupSub# w ?sub
  {-# inline sub #-}

mapSub :: (IVar -> IVar) -> (IVar -> I -> I) -> Sub -> Sub
mapSub domf f (Sub s) = mapDom domf (Sub (go (unsafeShiftR s 8) s' 0 (coerce len))) where
  len   = coerce $ cod (Sub s)
  shift = w2i (unsafeShiftL len 2 + 8)

  -- s with all elems zeroed out
  s' = unsafeShiftL (unsafeShiftR s shift) shift .|. 16

  go :: Word -> Word -> IVar -> IVar -> Word
  go inp out ix len
    | ix < len = let i' = f ix (I (inp .&. 15))
                 in go (unsafeShiftR inp 4)
                       (out .|. unsafeShiftL (coerce i')
                                             (w2i (coerce (unsafeShiftL (ix+2) 2))))
                       (ix + 1) len
    | True = out
{-# inline mapSub #-}

-- substitution composition
instance SubAction Sub where
  sub f = mapSub (\_ -> dom ?sub) (\_ i -> sub i) f
  {-# noinline sub #-}

goIsUnblocked :: NCofArg => IVarSet -> IVarSet -> Bool
goIsUnblocked is varset = popSmallestIS is
  (\is x -> matchIVar (lookupSub x ?cof)
     (\x -> memberIS x varset || goIsUnblocked is (insertIVarF x varset))
     True)
  False

-- A set of blocking ivars is still blocked under a cofibration
-- if all vars in the set are represented by distinct vars.
isUnblocked :: NCofArg => IVarSet -> Bool
isUnblocked is | emptyIS is = False
isUnblocked is = goIsUnblocked is mempty
{-# inline isUnblocked #-}

goIsUnblockedS :: SubArg => NCofArg => IVarSet -> IVarSet -> Bool
goIsUnblockedS is varset = popSmallestIS is
    (\is x -> matchIVar (lookupSub x ?sub)
      (\x -> matchIVar (lookupSub x ?cof)
        (\x -> memberIS x varset || goIsUnblockedS is (insertIVarF x varset))
        True)
      True)
    False

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
