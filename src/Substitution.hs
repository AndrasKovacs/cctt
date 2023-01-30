
module Substitution where

import Data.Foldable

import Common
import qualified IVarSet as IS
import Interval

{-|
Interval substitutions are nibble (4-bit) sequences stored in a 64-bit word.

  - 0-11 : mapped to I expressions
  - 12   : always mapped to I0 (the nibble 12)
  - 13   : always mapped to I1 (the nibble 13)
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
subToNibbles (Sub s) = go s where
  go 0 = []
  go n = n .&. 15 : go (unsafeShiftR n 4)

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

lookupSub# :: Word -> Sub -> I
lookupSub# w (Sub s) = I (unsafeShiftR s (unsafeShiftL (w2i w) 2) .&. 15)
{-# inline lookupSub# #-}

lookupSub :: IVar -> Sub -> I
lookupSub (IVar# x) s = lookupSub# x s
{-# inline lookupSub #-}

-- | Strict right fold over all (index, I) mappings in a substitution.
foldrSub :: forall b. (IVar -> I -> b -> b) -> b -> Sub -> b
foldrSub f b (Sub s) = go 0 (cod (Sub s)) s where
  go i l n | i < l = f i (I (n .&. 15)) $! go (i + 1) l (unsafeShiftR n 4)
  go i l n = b
{-# inline foldrSub #-}

-- | Extend a sub with an expression. Domain doesn't change.
ext :: Sub -> I -> Sub
ext (Sub s) i =
  let len = cod (Sub s)
      bl  = unsafeShiftL (coerce len) 2
  in setCod (len + 1)
            (Sub (s .&. complement (unsafeShiftL 15 (w2i bl))
                    .|. unsafeShiftL (coerce i) (w2i bl)))

subToList :: Sub -> [I]
subToList = foldrSub (\_ i is -> i:is) []

subFromList :: [I] -> Sub
subFromList is =
  let dom = case [x | IVar x <- is] of [] -> 0; is -> maximum is + 1
  in foldl' ext (emptySub dom) is

instance Show Sub where
  show = show . subToList

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
mapSub domf f (Sub s) = mapDom domf  (Sub (go s s' 0 (coerce len))) where
  len  = coerce $ cod (Sub s)
  blen = unsafeShiftL len 2
  s'   = unsafeShiftL (unsafeShiftR s (w2i blen)) (w2i blen)
  go :: Word -> Word -> IVar -> IVar -> Word
  go inp out ix len
    | ix < len = let i' = f ix (I (inp .&. 15))
                 in go (unsafeShiftR inp 4)
                       (out .|. unsafeShiftL (coerce i') (w2i (coerce (unsafeShiftL ix 2))))
                       (ix + 1) len
    | True     = out
{-# inline mapSub #-}

-- substitution composition
instance SubAction Sub where
  sub f = mapSub (\_ -> dom ?sub) (\_ i -> sub i) f
  {-# noinline sub #-}

-- A set of blocking ivars is still blocked under a cofibration
-- if all vars in the set are represented by distinct vars.
isUnblocked :: NCofArg => IS.IVarSet -> Bool
isUnblocked is = go is (mempty @IS.IVarSet) where
  go :: IS.IVarSet -> IS.IVarSet -> Bool
  go is varset = IS.popSmallest is
    (\is x -> matchIVar (lookupSub x ?cof)
       (\x -> IS.member x varset || go is (IS.insert x varset))
       True)
    False

isUnblockedS :: SubArg => NCofArg => IS.IVarSet -> Bool
isUnblockedS is = go is (mempty @IS.IVarSet) where
  go :: IS.IVarSet -> IS.IVarSet -> Bool
  go is varset = IS.popSmallest is
    (\is x -> matchIVar (lookupSub x ?sub)
      (\x -> matchIVar (lookupSub x ?cof)
        (\x -> IS.member x varset || go is (IS.insert x varset))
        True)
      True)
    False

instance SubAction IS.IVarSet where
  sub is = IS.foldl
    (\acc i -> IS.insertI (lookupSub i ?sub) acc)
    mempty is
  {-# noinline sub #-}

instance (SubAction a, SubAction b) => SubAction (a, b) where
  sub (a, b) = let x = sub a; y = sub b in (x, y)
  {-# inline sub #-}

instance (SubAction a, SubAction b, SubAction c) => SubAction (a, b, c) where
  sub (a, b, c) = let x = sub a; y = sub b; z = sub c in (x, y, z)
  {-# inline sub #-}
