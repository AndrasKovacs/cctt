

{-# OPTIONS --cubical --show-irrelevant --type-in-type #-}

module Notes2 where

open import Cubical.Foundations.Everything
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Glue

-- comp from hcomp & transp
comp' : {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) {φ : I} →
          (a : ∀ i → Partial φ (A i))
        → Sub (A i0) φ (a i0)
        → Sub (A i1) φ (a i1)
comp' {ℓ} A {φ} a a₀ =
  inS (hcomp {ℓ i1}{A i1}{φ}
       (λ i p → transp (λ j → A (i ∨ j)) i (a i p))
       (transp A i0 (outS a₀)))


-- transp from comp
transp' :
  ∀ {ℓ : I → Level}
    (A₀ : Type (ℓ i0))
    (φ : I)
    (A : ∀ i → Sub (Type (ℓ i)) φ λ _ → A₀)
  → (a₀ : outS (A i0))
  → Sub (outS (A i1)) φ λ {(φ = i1) → a₀}
transp' {ℓ} A₀ φ A a₀ = inS (comp (λ i → outS (A i)) (λ {i (φ = i1) → a₀}) a₀)


-- comp from hcomp & transport? I can't see how
comp'' : {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) {φ : I} →
          (a : ∀ i → Partial φ (A i))
        → Sub (A i0) φ (a i0)
        → Sub (A i1) φ (a i1)
comp'' {ℓ} A {φ} a a₀ =
  inS (hcomp {ℓ i1}{A i1}{φ}
    (λ i p → transp (λ j → A (i ∨ j)) i (a i p))
    (transport (λ i → A i) (outS a₀)))

-- The point of generalized transp is to allow splitting comp to transp and hcomp
--   which makes it possible to have HIT-s? Because they need formal hcomp, and possibly
--   formal transp?

-- transpⁱ (Glue [α ↦ (T, e)] A) ψ

-- only reduce if `α`, `T` and `e` are all constant in `i` under `ψ`.
