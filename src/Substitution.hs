
module Substitution where

import Common
import GHC.Exts

import qualified IVarSet as IS
import Interval

{-|
Interval substitutions are packed lists of interval expresssions in a 64-bit
word. The reserved "15" nibble value marks the end of the list. An ISub is keyed
by De Bruijn levels, and the 0 level maps to the least significant nibble. -}
newtype Sub = Sub Int
type SubArg = (?sub :: Sub)

{-|
Normalized cofibrations are also represented as interval substitutions. Here,
every ivar is mapped to the greatest (as a De Bruijn level) representative of
its equivalence class.
-}
type NCof = Sub

type NCofArg = (?cof :: NCof)

emptySub :: Sub
emptySub = Sub 15
{-# inline emptySub #-}

subLength :: Sub -> Int
subLength (Sub (I# x)) = 15 - unsafeShiftR (I# (word2Int# (clz64# (int2Word# x)))) 2
{-# inline subLength #-}

snocSub :: Sub -> I -> Sub
snocSub (Sub s@(I# s')) x =
  let elemBits = 60 - I# (word2Int# (clz64# (int2Word# s')))
      end      = unsafeShiftL 15 elemBits
      end'     = unsafeShiftL end 4
  in if elemBits == 60 then
    impossible
  else Sub (s .&. complement end                  -- zero out old end marker
            .|. end'                              -- write new end marker
            .|. unsafeShiftL (coerce x) elemBits) -- write new entry
{-# inline snocSub #-}

liftSub :: Sub -> Sub
liftSub (Sub s@(I# s')) =
  let elemBits = 60 - I# (word2Int# (clz64# (int2Word# s')))
      end      = unsafeShiftL 15 elemBits
      end'     = unsafeShiftL end 4
      entry    = coerce (unsafeShiftR elemBits 2)
  in if elemBits == 60 then
    impossible
  else Sub (s .&. complement end             -- zero out old end marker
            .|. end'                         -- write new end marker
            .|. unsafeShiftL entry elemBits) -- write new entry

-- | Strict right fold over all (index, I) mappings in a substitution.
foldrSub :: forall b. (Int -> I -> b -> b) -> b -> Sub -> b
foldrSub f b (Sub s) = go 0 s where
  go :: Int -> Int -> b
  go x s = case s .&. 15 of
    15 -> b
    i  -> f x (coerce i) $! go (x + 1) (unsafeShiftR s 4)
{-# inline foldrSub #-}

mapSub :: (Int -> I -> I) -> Sub -> Sub
mapSub f (Sub s) = Sub (go 0 0 0 s) where
  go :: Int -> Int -> Int -> Int -> Int
  go out x shift inp = case inp .&. 15 of
    15 -> unsafeShiftL 15 shift .|. out
    i  -> let i' = f x (coerce i) in
          go (unsafeShiftL (coerce i') shift .|. out)
             (x + 1)
             (shift + 4)
             (unsafeShiftR inp 4)
{-# inline mapSub #-}

subToList :: Sub -> [I]
subToList = foldrSub (\_ i acc -> i:acc) []

subFromList :: [I] -> Sub
subFromList is | length is > 15 = impossible
               | True = Sub (go is 0 0) where
  go []     shift s = unsafeShiftL 15 shift .|. s
  go (i:is) shift s = go is (shift + 4) (unsafeShiftL (coerce i) shift .|. s)

instance Show Sub where
  show = show . subToList

class SubAction a where
  sub :: a -> Sub -> a

lookupSub :: IVar -> Sub -> I
lookupSub (IVar# x) (Sub s)
  | 0 <= x && x < subLength (Sub s) = I (unsafeShiftR s (unsafeShiftL x 2) .&. 15)
  | True                            = impossible
{-# inline lookupSub #-}

instance SubAction I where
  sub (IVar x) s = lookupSub x s
  sub i        _ = i
  {-# inline sub #-}

-- substitution composition
instance SubAction Sub where
  sub f g = mapSub (\_ i -> sub i g) f
  {-# inline sub #-}

-- A set of blocking ivars is still blocked under a cofibration
-- if all vars in the set are represented by distinct vars.
isBlocked :: NCofArg => IS.IVarSet -> Bool
isBlocked is =
  IS.foldr (\x hyp varset -> case lookupSub x ?cof of
               IVar x | not (IS.member x varset) -> hyp (IS.insert x varset)
               _ -> False)
           (\_ -> True)
           is
           (mempty @IS.IVarSet)

isBlocked' :: SubArg => NCofArg => IS.IVarSet -> Bool
isBlocked' is =
  IS.foldr (\x hyp varset -> case lookupSub x ?sub of
               IVar x -> case lookupSub x ?cof of
                 IVar x | not (IS.member x varset) -> hyp (IS.insert x varset)
                 _ -> False
               _ -> False)
           (\_ -> True)
           is
           (mempty @IS.IVarSet)

instance SubAction IS.IVarSet where
  sub is s = IS.foldl
    (\acc i -> case lookupSub i s of
        IVar i -> IS.insert i acc
        _      -> impossible)
    mempty is
