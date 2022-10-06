{-# language UnboxedSums, UnboxedTuples #-}

{-|
Intervals, interval substitutions, cofibrations.
-}

module Cube where

-- import Debug.Trace

import Common
import GHC.Exts
import qualified IVarSet as IS

{-
Interval expressions are 4 bits (nibbles):
 reserved    : 15
 0           : 14
 1           : 13
 var (level) : 0-12

This makes it possible to represent an interval substitution of at most 13
dimensions in a single 64-bit word.
-}

-- data I = I0 | I1 | IVar Lvl
newtype I = I Int
  deriving Eq

insertI :: I -> IS.IVarSet -> IS.IVarSet
insertI (IVar x) is = IS.insert x is
insertI _        is = is

unpackI# :: I -> (# (# #) | (# #) | Int# #)
unpackI# (I (I# x)) = case x of
  14# -> (# (# #) |       |   #)
  13# -> (#       | (# #) |   #)
  x   -> (#       |       | x #)
{-# inline unpackI# #-}

pattern I0 :: I
pattern I0 <- (unpackI# -> (# (# #) | | #)) where I0 = I 14

pattern I1 :: I
pattern I1 <- (unpackI# -> (# | (# #) | #)) where I1 = I 13

pattern IVar :: IVar -> I
pattern IVar x <- (unpackI# -> (# | | (I# -> (IVar# -> x)) #)) where
  IVar x = I (coerce x)
{-# complete I0, I1, IVar #-}

instance Show I where
  showsPrec _ I0       acc = 'I':'0':acc
  showsPrec _ I1       acc = 'I':'1':acc
  showsPrec d (IVar x) acc = showParen (d > 10) (("IVar " ++).showsPrec 11 x) acc

{-
Interval substitutions are packed lists of interval expresssions in a 64-bit
word. The reserved "15" nibble value marks the end of the list. An ISub is keyed
by De Bruijn levels, and the 0 level maps to the least significant nibble.
-}

newtype Sub = Sub Int
type SubArg = (?sub :: Sub)
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

-- -- | Left fold over all (index, I) mappings in a substitution.
-- foldlSub :: forall b. (b -> Int -> I -> b) -> b -> Sub -> b
-- foldlSub f b (Sub s) = go b 0 s where
--   go :: b -> Int -> Int -> b
--   go b x s = case s .&. 15 of
--     15 -> b
--     i  -> let b' = f b x (coerce i) in go b' (x + 1) (unsafeShiftR s 4)
-- {-# inline foldlSub #-}

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

-- Syntactic cofibrations
--------------------------------------------------------------------------------

-- | Atomic equation.
data CofEq = CofEq IVar I
  deriving Show

-- | Conjunction of equations.
data Cof = CTrue | CAnd {-# unpack #-} CofEq Cof
  deriving Show

-- -- | Compose a Sub with a CofEq viewed as a single substitution.
-- compSubCofEq :: Sub -> CofEq -> Sub
-- compSubCofEq s (CofEq x i) = mapSub (\_ j -> if IVar x == j then i else j) s

-- -- | Evaluate a Cof in an environment. We get Nothing if the Cof is false,
-- --   Just otherwise. We also return the environment which is updated (conjuncted)
-- --   with the Cof.
-- evalCof :: Sub -> Cof -> (Sub, Maybe Cof)
-- evalCof s cof = go s CTrue cof where
--   go :: Sub -> Cof -> Cof -> (Sub, Maybe Cof)
--   go s acc = \case
--     CTrue                -> (s, Just acc)
--     CAnd (CofEq x i) cof -> case (lookupSub x s, sub i s) of

--       (IVar x, IVar x') ->
--         let eq | x < x' = CofEq x  (IVar x')
--                | True   = CofEq x' (IVar x )
--         in go (compSubCofEq s eq) (CAnd eq acc) cof

--       (IVar x, j)  -> let eq = CofEq x j  in go (compSubCofEq s eq) (CAnd eq acc) cof
--       (i, IVar x') -> let eq = CofEq x' i in go (compSubCofEq s eq) (CAnd eq acc) cof
--       (I0,     I0) -> go s acc cof
--       (I1,     I1) -> go s acc cof
--       _            -> (s, Nothing)
