{-# OPTIONS --safe --cubical #-}

module S1Bench where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.S1.Base
open import Cubical.Data.Nat
open import Cubical.Data.Int
open import Cubical.Data.Unit

forceℕ : ℕ → Unit
forceℕ zero    = tt
forceℕ (suc n) = forceℕ n

forceℤ : ℤ → Unit
forceℤ (pos n)    = forceℕ n
forceℤ (negsuc n) = forceℕ n

test1 : forceℤ (winding (intLoop (pos 10000))) ≡ tt
test1 = refl

-- test2 = forceℤ (winding (intLoop (neg 10)))
-- test3 = winding (intLoop (pos 10) ∙ intLoop (neg 10))
