
module Cubical.Interval where

import Common

-- Interval
--------------------------------------------------------------------------------

maxIVar :: IVar
maxIVar = 63
{-# inline maxIVar #-}

data I = IVar IVar | IAnd I I | IOr I I | I0 | I1
  deriving (Show)

-- | `IAnd` with shallow simplification.
iand :: I -> I -> I
iand I1 j = j
iand I0 j = I0
iand i I1 = i
iand i I0 = I0
iand i j  = IAnd i j

-- | `IOr` with shallow simplification.
ior :: I -> I -> I
ior I0 j = j
ior I1 j = I1
ior i I0 = i
ior i I1 = I1
ior i j  = IOr i j

-- | Sanity scope check.
isInScope :: IVar -> I -> Bool
isInScope dom = \case
  IVar i   -> i < dom
  IAnd i j -> isInScope dom i && isInScope dom j
  IOr  i j -> isInScope dom i && isInScope dom j
  _        -> True
