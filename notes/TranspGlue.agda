
{-# OPTIONS --cubical --show-irrelevant --type-in-type #-}

module TranspGlue where

open import Cubical.Foundations.Everything
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Glue

module Mod (A₀ A₁ : Type)(A≡ : A₀ ≡ A₁) (α : I) (e : ∀ i → A₀ ≃ A≡ i) where

  G : I → Type
  G i = Glue (A≡ i) {α} (λ _ → A₀ , e i)

  -- G is constantly A₀ under α
  constantG : ∀ i → Sub Type α λ _ → A₀
  constantG i = inS (G i)

  -- so transport works
  transpG : G i0 → G i1
  transpG = transp G α

  -- But the definition below computes to an ill-typed term.
  -- The computation rule assumes that A≡ i1 is definitionally equal to A≡ i0.
  f : G i0 → A₁
  f g₀ = unglue α (transpG g₀)

  unglue g₀ : A₀

  `a₀` is `unglue g₀ : A₀`

  A≡ i

  `α` (`psi` in the source)
