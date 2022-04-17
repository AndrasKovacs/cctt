
{-# OPTIONS --cubical --show-irrelevant #-}

module TranspGlueIssue where

open import Cubical.Foundations.Everything
open import Cubical.Core.Everything

open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Relation.Nullary.Base
open import Cubical.Data.Empty
open import Cubical.Data.Unit

the : ∀{l}(A : Type l) → A → A
the A x = x

data Bool₀ : Set where true false : Bool₀
data Bool₁ : Set where true false : Bool₁

true≢false : the Bool₁ true ≡ false → ⊥
true≢false p = subst (λ {true → Unit; false → ⊥}) p tt

Bool₁-discrete : Discrete Bool₁
Bool₁-discrete true  true  = yes refl
Bool₁-discrete true  false = no true≢false
Bool₁-discrete false true  = no (true≢false ∘ _⁻¹)
Bool₁-discrete false false = yes refl

Bool₁-set : isSet Bool₁
Bool₁-set = Discrete→isSet Bool₁-discrete

f : Bool₀ → Bool₁
f true  = true
f false = false

f-equiv : isEquiv f
fst (fst (equiv-proof f-equiv true)) = true
snd (fst (equiv-proof f-equiv true)) = refl
snd (equiv-proof f-equiv true) (true , p) i = (true , Bool₁-set _ _ refl p i)
snd (equiv-proof f-equiv true) (false , p) = rec (true≢false (p ⁻¹))
fst (fst (equiv-proof f-equiv false)) = false
snd (fst (equiv-proof f-equiv false)) = refl
snd (equiv-proof f-equiv false) (true , p) = rec (true≢false p)
snd (equiv-proof f-equiv false) (false , p) i = false , Bool₁-set _ _ refl p i

module _ (α : I) where

  lem : ∀ i → Bool₀ ≃ ua (f , f-equiv) i
  lem i = {!!}

  G : I → Type
  G i = Glue (ua (f , f-equiv) i) {α} (λ _ → Bool₀ , lem i)

  transpG : G i0 → G i1
  transpG g₀ = transp G α g₀

  foo = {!transpG!}


  bluh = transport (λ i → (ua (f , f-equiv)⁻¹) i)

  x = {!ua (f , f-equiv)!}

  -- x = {!bluh!}

-- -- module _ (α : I) where

-- --   A : Bool₀ ≡ Bool₁
-- --   A = ua (f , f-equiv)

-- --   T : Type
-- --   T = Bool₀

-- --   e : PathP (λ i → T ≃ A i) (idEquiv Bool₀) (f , f-equiv)
-- --   e = {!!}

-- --   Te : ∀ i → Σ Type λ T → T ≃ A i
-- --   Te i = Bool₀ , e i

-- --   G : I → Type
-- --   G i = Glue (A i) {α} (λ _ → Te i)

-- --   constantG : PartialP {ℓ-suc ℓ-zero} α λ {(α = i1) → G i0 ≡ G i1}
-- --   constantG (α = i1) = refl

-- --   foo = {!!}

-- module Mod (A₀ A₁ : Type)(A≃ : A₀ ≃ A₁) (α : I) (e : ∀ i → A₀ ≃ ua A≃ i) where

--   G : I → Type
--   G i = Glue (ua A≃ i) {α} (λ _ → A₀ , e i)

--   -- G is constantly A₀ under α
--   constantG : ∀ i → Sub Type α λ {(α = i1) → A₀}
--   constantG i = inS (G i)

--   -- so transport works
--   transpG : G i0 → G i1
--   transpG = transp G α

--   -- A₀ and A₁ are definitionally distinct. However, the computation rule for
--   -- transpG assumes that they are the same!

--   module _ (t : PartialP α λ _ → A₀)(a₀ : Sub A₀ α λ p → e i0 .fst (t p)) where

--     g₀ : G i0
--     g₀ = glue t (outS a₀)

--     g₁ : G i1
--     g₁ = {!transpG g₀!}



--   -- glue : ∀ {A : Type} {φ : I}
--   --        → {T : Partial  φ Type}
--   --        → {e : PartialP φ (λ p → T p ≃ A)}
--   --        → (t : PartialP φ T)
--   --        → (a : Sub A φ (λ p → e p .fst (t p)))
--   --        → Glue A (λ p → T p , e p)

record Prod (A B : Type) : Type where
  constructor prod
  field
    fst : A
    snd : B
open Prod

transpProd :
   ∀ α (A₀ B₀ : Type)
    (A : I → Sub Type α λ _ → A₀)
    (B : I → Sub Type α λ _ → B₀)
    (ab₀ : Prod (outS (A i0)) (outS (B i0)))
  → transp (λ i → Prod (outS (A i)) (outS (B i))) α ab₀ ≡
    prod (transp (λ i → outS (A i)) α (fst ab₀))
         (transp (λ i → outS (B i)) α (snd ab₀))
transpProd α A₀ B₀ A B ab₀ = refl
