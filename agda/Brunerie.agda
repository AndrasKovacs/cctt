-- Mostly self contained definitions of the numbers from: https://arxiv.org/abs/2302.00151
{-# OPTIONS --safe --cubical #-}
module Brunerie where

open import Cubical.Core.Primitives

open import Cubical.Foundations.Prelude using
  (_,_ ; fst ; snd ; _≡_ ; cong ; _∙_ ; refl ; isProp→isSet ; J ; sym ; isProp ; isSet ; isGroupoid ; is2Groupoid)
open import Cubical.Foundations.Equiv using
  (_≃_ ; isEquiv ; isPropIsEquiv ; idIsEquiv ; idEquiv)
open import Cubical.Foundations.HLevels using
  (hSet ; hGroupoid ; isOfHLevelTypeOfHLevel ; isOfHLevelPath ; isOfHLevelΠ ; isOfHLevel→isOfHLevelDep)
open import Cubical.Foundations.Univalence using
  (Glue ; ua)
open import Cubical.Data.Int using
  (ℤ ; pos ; neg ; isSetℤ ; sucPathℤ)
open import Cubical.Foundations.CartesianKanOps

private variable ℓ ℓ' : Level

-- S1
data S¹ : Type₀ where
  base : S¹
  loop : base ≡ base

helix : S¹ → Type₀
helix base     = ℤ
helix (loop i) = sucPathℤ i

rotLoop : (a : S¹) → a ≡ a
rotLoop base       = loop
rotLoop (loop i) j =
  hcomp (λ k → λ { (i = i0) → loop (j ∨ ~ k)
                 ; (i = i1) → loop (j ∧ k)
                 ; (j = i0) → loop (i ∨ ~ k)
                 ; (j = i1) → loop (i ∧ k)}) base

_·_ : S¹ → S¹ → S¹
base     · x = x
(loop i) · x = rotLoop x i

isPropFamS¹ : (P : S¹ → Type ℓ) (pP : (x : S¹) → isProp (P x)) (b0 : P base) →
              PathP (λ i → P (loop i)) b0 b0
isPropFamS¹ P pP b0 i = pP (loop i) (coe0→i (λ k → P (loop k)) i b0)
                                    (coe1→i (λ k → P (loop k)) i b0) i

rotIsEquiv : (a : S¹) → isEquiv (a ·_)
rotIsEquiv base = idIsEquiv S¹
rotIsEquiv (loop i) = isPropFamS¹ (λ x → isEquiv (x ·_))
                                  (λ x → isPropIsEquiv (x ·_))
                                  (idIsEquiv _) i

-- S2
data S² : Type₀ where
  base : S²
  surf : PathP (λ i → base ≡ base) refl refl

S²ToSetElim : {A : S² → Type ℓ}
            → ((x : S²) → isSet (A x))
            → A base
            → (x : S²) → A x
S²ToSetElim set b base = b
S²ToSetElim {A = A} set b (surf i j) =
  isOfHLevel→isOfHLevelDep 2 {S²}{λ z → A z} set {base}{base} b b {a0 = refl} {a1 = refl} refl refl surf i j


-- Join
data join (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  inl : A → join A B
  inr : B → join A B
  push : ∀ a b → inl a ≡ inr b

-- SetTruncation
data ∥_∥₀ (A : Type ℓ) : Type ℓ where
  ∣_∣₀ : A → ∥ A ∥₀
  squash₀ : ∀ (x y : ∥ A ∥₀) (p q : x ≡ y) → p ≡ q

rec₀ : {A : Type ℓ} {B : Type ℓ'} → isSet B → (A → B) → ∥ A ∥₀ → B
rec₀ Bset f ∣ x ∣₀ = f x
rec₀ Bset f (squash₀ x y p q i j) =
 Bset (rec₀ Bset f x) (rec₀ Bset f y) (cong (rec₀ Bset f) p) (cong (rec₀ Bset f) q) i j


-- GroupoidTruncation
data ∥_∥₁ (A : Type ℓ) : Type ℓ where
  ∣_∣₁ : A → ∥ A ∥₁
  squash₁ : ∀ (x y : ∥ A ∥₁) (p q : x ≡ y) (r s : p ≡ q) → r ≡ s

rec₁ : {A : Type ℓ} {B : Type ℓ'} → isGroupoid B → (A → B) → ∥ A ∥₁ → B
rec₁ gB f ∣ x ∣₁ = f x
rec₁ gB f (squash₁ x y p q r s i j k) =
  gB (rec₁ gB f x) (rec₁ gB f y)
     (λ n → rec₁ gB f (r i0 n))
     (λ n → rec₁ gB f (r i1 n))
     (λ m n → rec₁ gB f (r m n)) (λ m n → rec₁ gB f (s m n)) i j k


-- 2GroupoidTruncation
data ∥_∥₂ (A : Type ℓ) : Type ℓ where
  ∣_∣₂ : A → ∥ A ∥₂
  squash₂ : ∀ (x y : ∥ A ∥₂) (p q : x ≡ y) (r s : p ≡ q) (t u : r ≡ s) → t ≡ u

rec₂ : ∀ {A : Type ℓ} {B : Type ℓ'} → is2Groupoid B → (A → B) → ∥ A ∥₂ → B
rec₂ gB f ∣ x ∣₂ = f x
rec₂ gB f (squash₂ a b p q r s t u i j k l) =
  gB (rec₂ gB f a)
     (rec₂ gB f b)
     (λ o → rec₂ gB f (p o))
     (λ o → rec₂ gB f (q o))
     (λ n o → rec₂ gB f (t i0 n o))
     (λ n o → rec₂ gB f (t i1 n o))
     (λ m n o → rec₂ gB f (t m n o))
     (λ m n o → rec₂ gB f (u m n o))
     i j k l

elim₂ : {A : Type ℓ} {B : ∥ A ∥₂ → Type ℓ}
       (bG : (x : ∥ A ∥₂) → is2Groupoid (B x))
       (f : (x : A) → B ∣ x ∣₂) (x : ∥ A ∥₂) → B x
elim₂ bG f ∣ x ∣₂ = f x
elim₂ {A = A}{B} bG f (squash₂ a b p q r s u v i j k l) =
  isOfHLevel→isOfHLevelDep 4 {A = ∥ A ∥₂}{λ z → B z} bG
    {a}
    {b}
    (elim₂ {A = A}{B} bG f a)
    (elim₂ {A = A}{B} bG f b)
    {p}
    {q}
    (λ l₁ → elim₂ bG f (p l₁))
    (λ l₁ → elim₂ bG f (q l₁))
    {u i0}
    {u i1}
    (λ k₁ l₁ → elim₂ bG f (u i0 k₁ l₁))
    (λ k₁ l₁ → elim₂ bG f (u i1 k₁ l₁))
    {u}
    {v}
    (λ j k l → elim₂ bG f (u j k l)) (λ j k l → elim₂ bG f (v j k l))
    (squash₂ a b p q r s u v)
    i j k l


-- Susp
data Susp (A : Type ℓ) : Type ℓ where
  north : Susp A
  south : Susp A
  merid : (a : A) → north ≡ south


-- Pointed
Pointed₀ : Type₁
Pointed₀ = Σ[ X ∈ Type₀ ] X

S¹∙ S²∙ : Pointed₀
S¹∙ = (S¹ , base)
S²∙ = (S² , base)

Susp∙ : Type₀ → Pointed₀
Susp∙ A = Susp A , north

∥_∥₁∙ ∥_∥₂∙ : Pointed₀ → Pointed₀
∥ A , a ∥₁∙ = ∥ A ∥₁ , ∣ a ∣₁
∥ A , a ∥₂∙ = ∥ A ∥₂ , ∣ a ∣₂

Ω Ω² : Pointed₀ → Pointed₀
Ω (_ , a) = ((a ≡ a) , refl)
Ω² p = Ω (Ω p)

-- The maps
σ : S² → Ω (Susp∙ S²) .fst
σ x = merid x ∙ sym (merid base)

S¹×S¹→S² : S¹ → S¹ → S²
S¹×S¹→S² base y = base
S¹×S¹→S² (loop i) base = base
S¹×S¹→S² (loop i) (loop j) = surf i j

f7 : Ω (Susp∙ S²) .fst → ∥ S² ∥₂
f7 = encode north
  where
  _+₂_ : ∥ S² ∥₂ → ∥ S² ∥₂ → ∥ S² ∥₂
  _+₂_ = elim₂ (λ _ → isOfHLevelΠ 4 λ _ → squash₂)
                λ { base x → x
                  ; (surf i j) x → surfc x i j}
    where
    surfc : (x : ∥ S² ∥₂) → Ω² (∥ S² ∥₂ , x) .fst
    surfc = elim₂ (λ _ → isOfHLevelPath 4 (isOfHLevelPath 4 squash₂ _ _) _ _)
                  (S²ToSetElim (λ _ → squash₂ _ _ _ _) λ i j → ∣ surf i j ∣₂)

  ∥S²∥₂≃∥S²∥₂ : (x : S²) → ∥ S² ∥₂ ≃ ∥ S² ∥₂
  fst (∥S²∥₂≃∥S²∥₂ x) = ∣ x ∣₂ +₂_
  snd (∥S²∥₂≃∥S²∥₂ x) = help x
    where
    help : (x : _) → isEquiv (λ y → ∣ x ∣₂ +₂ y)
    help = S²ToSetElim (λ _ → isProp→isSet (isPropIsEquiv _)) (idEquiv _ .snd)

  Code : Susp S² → Type₀
  Code north = ∥ S² ∥₂
  Code south = ∥ S² ∥₂
  Code (merid a i) = ua (∥S²∥₂≃∥S²∥₂ a) i

  encode : (x : Susp S²) →  north ≡ x → Code x
  encode x = J (λ x p → Code x) ∣ base ∣₂

g8 : Ω² ∥ S²∙ ∥₂∙ .fst → Ω ∥ S¹∙ ∥₁∙ .fst
g8 p i = encodeTruncS² (p i)
  where
  HopfS² : S² → Type₀
  HopfS² base = S¹
  HopfS² (surf i j) = Glue S¹ (λ { (i = i0) → _ , idEquiv S¹
                                 ; (i = i1) → _ , idEquiv S¹
                                 ; (j = i0) → _ , idEquiv S¹
                                 ; (j = i1) → _ , _ , rotIsEquiv (loop i) } )

  codeS² : S² → hGroupoid _
  codeS² s = ∥ HopfS² s ∥₁ , squash₁

  codeTruncS² : ∥ S² ∥₂ → hGroupoid _
  codeTruncS² = rec₂ (isOfHLevelTypeOfHLevel 3) codeS²

  encodeTruncS² : Ω ∥ S²∙ ∥₂∙ .fst → ∥ S¹ ∥₁
  encodeTruncS² p = coe0→1 (λ i → codeTruncS² (p i) .fst) ∣ base ∣₁

g9 : Ω ∥ S¹∙ ∥₁∙ .fst → ∥ ℤ ∥₀
g9 p = coe0→1 (λ i → codeTruncS¹ (p i) .fst) ∣ pos 0 ∣₀
  where
  codeS¹ : S¹ → hSet _
  codeS¹ s = ∥ helix s ∥₀ , squash₀

  codeTruncS¹ : ∥ S¹ ∥₁ → hSet _
  codeTruncS¹ = rec₁ (isOfHLevelTypeOfHLevel 2) codeS¹

-- Use trick to eliminate away the truncation last
g10 : ∥ ℤ ∥₀ → ℤ
g10 = rec₀ isSetℤ (λ x → x)

-- TODO: define η₁ and η₂ and some more maps

-- Original η₃ as in the paper
η₃ : join S¹ S¹ → Susp S²
η₃ (inl x) = north
η₃ (inr x) = north
η₃ (push a b i) =
  (sym (σ (S¹×S¹→S² a b)) ∙ sym (σ (S¹×S¹→S² a b))) i

-- Dropping the syms makes it compute fast (why?! maybe some slow inverse map gets applied with the sym?)
η₃' : join S¹ S¹ → Susp S²
η₃' (inl x) = north
η₃' (inr x) = north
η₃' (push a b i) =
  (σ (S¹×S¹→S² a b) ∙ σ (S¹×S¹→S² a b)) i

-- Remark: dropping only one sym does not seem to make it fast enough

-- Brunerie numbers

β₃ : ℤ
β₃ = g10 (g9 (g8 λ i j → f7 λ k → η₃ (push (loop i) (loop j) k)))

-- This does not terminate fast
-- β₃≡-2 : β₃ ≡ -2
-- β₃≡-2 = refl

β₃' : ℤ
β₃' = g10 (g9 (g8 λ i j → f7 λ k → η₃' (push (loop i) (loop j) k)))

-- This terminates fast
β₃'≡-2 : β₃' ≡ -2
β₃'≡-2 = refl

β₃'-pos : ℤ
β₃'-pos = g10 (g9 (g8 λ i j → f7 λ k → η₃' (push (loop (~ i)) (loop j) k)))

brunerie'≡2 : β₃'-pos ≡ pos 2
brunerie'≡2 = refl
