
module Cubical.Interval where

import GHC.Exts
import Common

-- Interval expressions are 64 bits: I0 is 0, I1 is 1, any other value N
-- represents IVar (n - 2).

-- We use 64-bit bitsets of IVar-s.
maxIVar :: IVar
maxIVar = 63
{-# inline maxIVar #-}

-- data I = I0 | I1 | IVar IVar
newtype I = I {unI :: Word}
  deriving Eq

-- | Unsafely flip an I which is known to be 0 or 1.
flip# :: I -> I
flip# (I w) = I (1 - w)
{-# inline flip# #-}

unpackI# :: I -> (# (# #) | (# #) | Word# #)
unpackI# (I (W# x)) = case x of
  0## -> (# (# #) |       |                    #)  -- I0
  1## -> (#       | (# #) |                    #)  -- I1
  x   -> (#       |       | x `minusWord#` 2## #)  -- IVar
{-# inline unpackI# #-}

pattern I0 :: I
pattern I0 <- (unpackI# -> (# (# #) | | #)) where I0 = I 0
{-# inline I0 #-}

pattern I1 :: I
pattern I1 <- (unpackI# -> (# | (# #) | #)) where I1 = I 1
{-# inline I1 #-}

pattern IVar :: IVar -> I
pattern IVar x <- (unpackI# -> (# | | (W# -> (IVar# -> x)) #)) where
  IVar (IVar# x) = I (x + 2)
{-# inline IVar #-}
{-# complete I0, I1, IVar #-}

matchIVar :: I -> (IVar -> a) -> a -> a
matchIVar (I x) f ~a | x >= 2 = f (IVar# (x - 2))
                     | True   = a
{-# inline matchIVar #-}

instance Show I where
  showsPrec _ I0       acc = 'I':'0':acc
  showsPrec _ I1       acc = 'I':'1':acc
  showsPrec d (IVar x) acc = showParen (d > 10) (("IVar " ++).showsPrec 11 x) acc
