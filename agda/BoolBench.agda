{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Bool


BoolPathN : ℕ → Bool ≡ Bool
BoolPathN n = iter n (λ p → p ∙ notEq) notEq

fun : ℕ → Bool → Bool
fun n x = transport (BoolPathN n) x

val : ℕ → Bool
val n = transport (BoolPathN n) true

-- test : val 350 ≡ false
-- test = refl

-- all|internal|modules|definitions|sharing|serialize|constraints|metas|interactive|conversion)


foo : (A : Set)(x : A) → I → A
foo A x i = hcomp {φ = ~ (i ∧ ~ i)} (λ _ → λ {(i = i0) → x; (i = i1) → x}) x

bar : (A : Set)(x : A) → I → A
bar A x i = hcomp {φ = ~ i ∨ i} (λ _ → λ {(i = i0) → x; (i = i1) → x}) x

baz : foo ≡ bar
baz = refl
