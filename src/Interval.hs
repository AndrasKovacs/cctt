{-# language UnboxedTuples #-}

module Interval where

{-|
Interval expressions are 4 bits (nibbles):
 0           : 14
 1           : 13
 var (level) : 0-12

This makes it possible to represent an interval substitution of at most 13
dimensions in a single 64-bit word.
-}

import GHC.Exts
import Common

-- data I = I0 | I1 | IVar IVar
newtype I = I Word
  deriving Eq

unpackI# :: I -> (# (# #) | (# #) | Word# #)
unpackI# (I (W# x)) = case x of
  14## -> (# (# #) |       |   #)
  13## -> (#       | (# #) |   #)
  x    -> (#       |       | x #)
{-# inline unpackI# #-}

pattern I0 :: I
pattern I0 <- (unpackI# -> (# (# #) | | #)) where I0 = I 14

pattern I1 :: I
pattern I1 <- (unpackI# -> (# | (# #) | #)) where I1 = I 13

pattern IVar :: IVar -> I
pattern IVar x <- (unpackI# -> (# | | (W# -> (IVar# -> x)) #)) where
  IVar x = I (coerce x)
{-# complete I0, I1, IVar #-}

matchIVar :: I -> (IVar -> a) -> a -> a
matchIVar (I x) f ~a | x < 13 = f (IVar# x)
                     | True   = a
{-# inline matchIVar #-}

instance Show I where
  showsPrec _ I0       acc = 'I':'0':acc
  showsPrec _ I1       acc = 'I':'1':acc
  showsPrec d (IVar x) acc = showParen (d > 10) (("IVar " ++).showsPrec 11 x) acc

type IDomArg = (?idom :: IVar)   -- fresh IVar
