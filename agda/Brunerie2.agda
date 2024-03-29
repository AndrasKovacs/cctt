-- Mostly self contained definitions of the numbers from: https://arxiv.org/abs/2302.00151
{-# OPTIONS --safe --cubical #-}
module Brunerie2 where

open import Cubical.Core.Primitives

open import Cubical.Foundations.Prelude using
  (_,_ ; fst ; snd ; _≡_ ; cong ; _∙_ ; refl ; isProp→isSet ; J ; sym ; isProp ; isSet ; isGroupoid ; is2Groupoid;
   doubleComp-faces)
open import Cubical.Foundations.Equiv using
  (_≃_ ; isEquiv ; isPropIsEquiv ; idIsEquiv ; idEquiv)
open import Cubical.Foundations.HLevels using
  (hSet ; hGroupoid ; isOfHLevelTypeOfHLevel ; isOfHLevelPath ; isOfHLevelΠ ; isOfHLevel→isOfHLevelDep ; is2GroupoidΠ)
open import Cubical.Foundations.Univalence using
  (Glue ; ua)
open import Cubical.Data.Int using
  (ℤ ; pos ; neg ; isSetℤ ; sucPathℤ)
open import Cubical.Foundations.CartesianKanOps

private variable ℓ ℓ' ℓ'' : Level

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
S²ToSetElim set b (surf i j) =
  isOfHLevel→isOfHLevelDep 2 set b b {a0 = refl} {a1 = refl} refl refl surf i j

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
  Bset _ _ (cong (rec₀ Bset f) p) (cong (rec₀ Bset f) q) i j


-- GroupoidTruncation
data ∥_∥₁ (A : Type ℓ) : Type ℓ where
  ∣_∣₁ : A → ∥ A ∥₁
  squash₁ : ∀ (x y : ∥ A ∥₁) (p q : x ≡ y) (r s : p ≡ q) → r ≡ s

rec₁ : {A : Type ℓ} {B : Type ℓ'} → isGroupoid B → (A → B) → ∥ A ∥₁ → B
rec₁ gB f ∣ x ∣₁ = f x
rec₁ gB f (squash₁ x y p q r s i j k) =
  gB _ _ _ _ (λ m n → rec₁ gB f (r m n)) (λ m n → rec₁ gB f (s m n)) i j k


-- 2GroupoidTruncation
data ∥_∥₂ (A : Type ℓ) : Type ℓ where
  ∣_∣₂ : A → ∥ A ∥₂
  squash₂ : ∀ (x y : ∥ A ∥₂) (p q : x ≡ y) (r s : p ≡ q) (t u : r ≡ s) → t ≡ u

rec₂ : ∀ {A : Type ℓ} {B : Type ℓ'} → is2Groupoid B → (A → B) → ∥ A ∥₂ → B
rec₂ gB f ∣ x ∣₂ = f x
rec₂ gB f (squash₂ _ _ _ _ _ _ t u i j k l) =
  gB _ _ _ _ _ _ (λ m n o → rec₂ gB f (t m n o)) (λ m n o → rec₂ gB f (u m n o))
     i j k l

-- rec₂Bin : ∀ {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → is2Groupoid C → (A → B → C) → ∥ A ∥₂ → ∥ B ∥₂ → C
-- rec₂Bin gB f = rec₂ (is2GroupoidΠ λ _ → gB) λ x → rec₂ gB (f x)

elim₂ : {A : Type ℓ} {B : ∥ A ∥₂ → Type ℓ}
       (bG : (x : ∥ A ∥₂) → is2Groupoid (B x))
       (f : (x : A) → B ∣ x ∣₂) (x : ∥ A ∥₂) → B x
elim₂ bG f ∣ x ∣₂ = f x
elim₂ bG f (squash₂ x y p q r s u v i j k l) =
  isOfHLevel→isOfHLevelDep 4 bG _ _ _ _ _ _
    (λ j k l → elim₂ bG f (u j k l)) (λ j k l → elim₂ bG f (v j k l))
    (squash₂ x y p q r s u v)
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
f7 p = coe0→1 (λ i → Code (p i)) ∣ base ∣₂
  where
  _+₂_ : ∥ S² ∥₂ → ∥ S² ∥₂ → ∥ S² ∥₂
  _+₂_ = rec₂ {A = S²}{∥ S² ∥₂ → ∥ S² ∥₂} (is2GroupoidΠ {A = ∥ S² ∥₂}{_}{λ _ → ∥ S² ∥₂} λ _ → squash₂)
             (λ { base x → x
               ; (surf i j) x → surfc x i j})
    where
    surfc : (x : ∥ S² ∥₂) → refl {x = x} ≡ refl {x = x}
    surfc = elim₂ {A = S²}{λ x → refl {x = x} ≡ refl}
                  (λ x → isOfHLevelPath {A = x ≡ x} 4 (isOfHLevelPath {A = ∥ S² ∥₂} 4 squash₂ x x) refl refl)
                  (S²ToSetElim {A = λ x → refl {x = ∣ x ∣₂} ≡ refl}
                               (λ x → squash₂ ∣ x ∣₂ ∣ x ∣₂ refl refl)
                               (λ i j → ∣ surf i j ∣₂))

  ∥S²∥₂≃∥S²∥₂ : (x : S²) → ∥ S² ∥₂ ≃ ∥ S² ∥₂
  fst (∥S²∥₂≃∥S²∥₂ x) = ∣ x ∣₂ +₂_
  snd (∥S²∥₂≃∥S²∥₂ x) = help x
    where
    help : (x : S²) → isEquiv {A = ∥ S² ∥₂}{∥ S² ∥₂} (∣ x ∣₂ +₂_)
    help = S²ToSetElim {A = λ x → isEquiv (_+₂_ ∣ x ∣₂)}
                       (λ x → isProp→isSet {A = isEquiv {A = ∥ S² ∥₂}{∥ S² ∥₂} (_+₂_ ∣ x ∣₂)}
                                           (isPropIsEquiv {A = ∥ S² ∥₂}{B = ∥ S² ∥₂} (_+₂_ ∣ x ∣₂)))
                       (idIsEquiv ∥ S² ∥₂)

  Code : Susp S² → Type₀
  Code north = ∥ S² ∥₂
  Code south = ∥ S² ∥₂
  Code (merid a i) = ua (∥S²∥₂≃∥S²∥₂ a) i

g8 : Ω² ∥ S²∙ ∥₂∙ .fst → Ω ∥ S¹∙ ∥₁∙ .fst
g8 p i =  coe0→1 (λ j → codeTruncS² (p i j) .fst) ∣ base ∣₁
  where
  HopfS² : S² → Type₀
  HopfS² base = S¹
  HopfS² (surf i j) = Glue S¹ (λ { (i = i0) → S¹ , idEquiv S¹
                                 ; (i = i1) → S¹ , idEquiv S¹
                                 ; (j = i0) → S¹ , idEquiv S¹
                                 ; (j = i1) → S¹ , (loop i) ·_  , rotIsEquiv (loop i) } )

  codeTruncS² : ∥ S² ∥₂ → hGroupoid ℓ-zero
  codeTruncS² = rec₂ {A = S²}{hGroupoid ℓ-zero}
                     (isOfHLevelTypeOfHLevel 3)
                     (λ s → ∥ HopfS² s ∥₁ , squash₁)

codeTruncS¹ : ∥ S¹ ∥₁ → hSet _
codeTruncS¹ = rec₁ {A = S¹}{hSet _} (isOfHLevelTypeOfHLevel 2) (λ s → ∥ helix s ∥₀ , squash₀)

g9 : Ω ∥ S¹∙ ∥₁∙ .fst → ∥ ℤ ∥₀
g9 p = coe0→1 (λ i → codeTruncS¹ (p i) .fst) ∣ pos 0 ∣₀

-- Use trick to eliminate away the truncation last
g10 : ∥ ℤ ∥₀ → ℤ
g10 = rec₀ {A = ℤ}{ℤ} isSetℤ (λ x → x)

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

----------------------------------------------------------------------------------------------------

v1 : (i j k : I) → Susp S²
v1 i j k = η₃' (push (loop i) (loop j) k)

data List (A : Set) : Set where
  nil  : List A
  cons : A → List A → List A

bnd3 : {A : Set}(f : I → I → I → A) → List A
bnd3 f =
  cons (f i0 i0 i0) (
  cons (f i0 i0 i1) (
  cons (f i0 i1 i0) (
  cons (f i0 i1 i1) (
  cons (f i1 i0 i0) (
  cons (f i1 i0 i1) (
  cons (f i1 i1 i0) (
  cons (f i1 i1 i1) nil)))))))

bnd2 : {A : Set}(f : I → I → A) → List A
bnd2 f =
  cons (f i0 i0) (
  cons (f i0 i1) (
  cons (f i1 i0) (
  cons (f i1 i1) nil)))

v2 : (i j : I) → ∥ S² ∥₂
v2 i j = f7 λ k → η₃' (push (loop i) (loop j) k)

-- nf doesn't terminate
v3 : (Ω ∥ S¹∙ ∥₁∙) .fst
v3 = g8 (λ i j → f7 λ k → η₃' (push (loop i) (loop j) k))

v4 = g9 v3 -- ∣ ℤ.negsuc 1 ∣₀

v5 = g10 v4

foo : ℤ
foo = -2

--------------------------------------------------------------------------------

-- This terminates fast
β₃'≡-2 : β₃' ≡ -2
β₃'≡-2 = refl

β₃'-pos : ℤ
β₃'-pos = g10 (g9 (g8 λ i j → f7 λ k → η₃' (push (loop (~ i)) (loop j) k)))

brunerie'≡2 : β₃'-pos ≡ pos 2
brunerie'≡2 = refl
