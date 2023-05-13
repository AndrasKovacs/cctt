
module Cubical.Interval where

import GHC.Exts
import Common

-- Interval expressions are 64 bits: I0 is 0, I1 is 1, any other value N
-- represents IVar (n - 2).

-- We use 64-bit bitsets of I-s in cofibrations, where we spend 0 and 1 on
-- constants, so the largest representable IVar is 61.
maxIVar :: IVar
maxIVar = 61
{-# inline maxIVar #-}

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

matchIVar :: I -> (IVar -> a) -> a -> a
matchIVar (I x) f ~a | x >= 2 = f (IVar# (x - 2))
                     | True   = a
{-# inline matchIVar #-}

instance Show I where
  showsPrec _ I0       acc = 'I':'0':acc
  showsPrec _ I1       acc = 'I':'1':acc
  showsPrec d (IVar x) acc = showParen (d > 10) (("IVar " ++).showsPrec 11 x) acc
