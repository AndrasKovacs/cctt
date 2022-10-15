
module Substitution where

import Common
import qualified IVarSet as IS
import Interval

-- import Debug.Trace

{-|
Interval substitutions are length-postfixed lists of interval expressions,
stored in a 64-bit word. The most significant 4-bit (nibble) is the length. -}
newtype Sub = Sub Word
  deriving Eq via Word

type SubArg = (?sub :: Sub)  -- ImplicitParams

{-|
Normalized cofibrations are also represented as interval substitutions. Here,
every ivar is mapped to the greatest (as a De Bruijn level) representative of
its equivalence class.
-}
type NCof = Sub
type NCofArg = (?cof :: NCof)

-- nibblesToWord :: [Word64] -> Word64
-- nibblesToWord ns = go 0 0 ns where
--   go shift acc []     = acc
--   go shift acc (n:ns) = go (shift + 4) (unsafeShiftL n shift .|. acc) ns

-- wordToNibbles :: Word64 -> [Word64]
-- wordToNibbles = go where
--   go 0 = []
--   go n = n .&. 15 : go (unsafeShiftR n 4)

emptySub# :: Word
emptySub# = 1070935975390360080 -- nibblesToWord [0..14]
{-# inline emptySub# #-}

emptySub :: Sub
emptySub = Sub emptySub#
{-# inline emptySub #-}

idSub :: IVar -> Sub
idSub (IVar# x) = Sub (emptySub# .|. unsafeShiftL x 60)
{-# inline idSub #-}

subLength :: Sub -> Word
subLength (Sub n) = unsafeShiftR n 60
{-# inline subLength #-}

lookupSub :: IVar -> Sub -> I
lookupSub (IVar# x) (Sub s) =
  I (unsafeShiftR s (unsafeShiftL (w2i x) 2) .&. 15)
{-# inline lookupSub #-}

-- | Strict right fold over all (index, I) mappings in a substitution.
foldrSub :: forall b. (IVar -> I -> b -> b) -> b -> Sub -> b
foldrSub f b (Sub s) = go 0 (IVar# (subLength (Sub s))) s where
  go i l n | i < l = f i (I (n .&. 15)) $! go (i + 1) l (unsafeShiftR n 4)
  go i l n = b
{-# inline foldrSub #-}

subToList :: Sub -> [I]
subToList = foldrSub (\_ i is -> i:is) []

subFromList :: [I] -> Sub
subFromList is = Sub (go acc 0 is .|. unsafeShiftL (i2w len) 60) where
  len  = length is
  blen = unsafeShiftL len 2
  acc  = unsafeShiftL (unsafeShiftR emptySub# blen) blen

  go :: Word -> Int -> [I] -> Word
  go acc shift []     = acc
  go acc shift (i:is) = go (unsafeShiftL (coerce i) shift .|. acc) (shift + 4)  is

instance Show Sub where
  show = show . subToList

mapSub :: (IVar -> I -> I) -> Sub -> Sub
mapSub f (Sub s) = Sub (go s s' 0 (coerce len)) where
  len  = subLength (Sub s)
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

-- 0 bits where the length is, else 1
lengthUnMask# :: Word
lengthUnMask# = 1152921504606846975

hasAction :: Sub -> Bool
hasAction (Sub s) = (s .&. lengthUnMask#) /= emptySub#
{-# inline hasAction #-}

class SubAction a where
  goSub :: a -> Sub -> a

sub :: SubAction a => a -> Sub -> a
sub ~a s = if hasAction s then goSub a s else a
{-# inline sub #-}

instance SubAction I where
  goSub (IVar x) s = lookupSub x s
  goSub i        _ = i
  {-# inline goSub #-}

-- substitution composition
instance SubAction Sub where
  goSub f g = mapSub (\_ i -> sub i g) f

-- A set of blocking ivars is still blocked under a cofibration
-- if all vars in the set are represented by distinct vars.
isUnblocked :: NCofArg => IS.IVarSet -> Bool
isUnblocked is =
  IS.foldr (\x hyp varset -> case lookupSub x ?cof of
               IVar x | not (IS.member x varset) -> hyp (IS.insert x varset)
               _ -> True)
           (\_ -> False)
           is
           (mempty @IS.IVarSet)

isUnblocked' :: SubArg => NCofArg => IS.IVarSet -> Bool
isUnblocked' is =
  IS.foldr (\x hyp varset -> case lookupSub x ?sub of
               IVar x -> case lookupSub x ?cof of
                 IVar x | not (IS.member x varset) -> hyp (IS.insert x varset)
                 _ -> True
               _ -> True)
           (\_ -> False)
           is
           (mempty @IS.IVarSet)

instance SubAction IS.IVarSet where
  goSub is s = IS.foldl
    (\acc i -> IS.insertI (lookupSub i s) acc)
    mempty is
