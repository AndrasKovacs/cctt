{-# OPTIONS --safe --cubical #-}
module HLevelsTemp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Data.Sigma

hSet hGroupoid : ∀ ℓ → Type (ℓ-suc ℓ)
hSet       ℓ = Σ[ A ∈ Type ℓ ] isSet A
hGroupoid  ℓ = Σ[ A ∈ Type ℓ ] isGroupoid A

private
  variable
    ℓ : Level
    A : Type ℓ
    B : A → Type ℓ

isPropIsSet : isProp (isSet A)
isPropIsSet {A = A} f g i a b = isPropIsProp {A = a ≡ b} (f a b) (g a b) i

isPropIsGroupoid : isProp (isGroupoid A)
isPropIsGroupoid {A = A} f g i a b = isPropIsSet {A = a ≡ b} (f a b) (g a b) i

isPropΣ : isProp A → ((x : A) → isProp (B x)) → isProp (Σ A B)
isPropΣ pA pB t u = Σ≡Prop pB (pA (t .fst) (u .fst))

isPropRetract : {B : Type ℓ} (f : A → B) (g : B → A) (h : (x : A) → g (f x) ≡ x) → isProp B → isProp A
isPropRetract f g h p x y i =
  hcomp (λ j → λ { (i = i0) → h x j
                 ; (i = i1) → h y j})
        (g (p (f x) (f y) i))

isSetRetract : {B : Type ℓ} (f : A → B) (g : B → A) (h : (x : A) → g (f x) ≡ x) → isSet B → isSet A
isSetRetract f g h set x y p q i j =
  hcomp (λ k → λ { (i = i0) → h (p j) k
                 ; (i = i1) → h (q j) k
                 ; (j = i0) → h x k
                 ; (j = i1) → h y k})
        (g (set (f x) (f y) (cong f p) (cong f q) i j))

isGroupoidRetract : {B : Type ℓ} (f : A → B) (g : B → A) (h : (x : A) → g (f x) ≡ x) → isGroupoid B → isGroupoid A
isGroupoidRetract f g h grp x y p q P Q i j k =
  hcomp ((λ l → λ { (i = i0) → h (P j k) l
                  ; (i = i1) → h (Q j k) l
                  ; (j = i0) → h (p k) l
                  ; (j = i1) → h (q k) l
                  ; (k = i0) → h x l
                  ; (k = i1) → h y l}))
       (g (grp (f x) (f y) (cong f p) (cong f q) (cong (cong f) P) (cong (cong f) Q) i j k))

congFst⁻ : (pB : (x : A) → isProp (B x)) (t u : Σ A B) → t .fst ≡ u .fst → t ≡ u
congFst⁻ {B = B} pB t u q i = (q i) ,
          hcomp (λ j → λ { (i = i0) → pB (t .fst) (t .snd) (t .snd) j
                         ; (i = i1) → pB (u .fst) (coe0→1 (λ k → B (q k)) (t .snd)) (u .snd) j })
                (coe0→i (λ x → B (q x)) i (t .snd))

congFst⁻-congFst : (pB : (x : A) → isProp (B x)) (t u : Σ A B) → (p : t ≡ u) → congFst⁻ pB t u (cong fst p) ≡ p
congFst⁻-congFst {B = B} pB t u p j i =
  (p i .fst) ,
  (hcomp {A = B (p i .fst)}
         (λ k → λ { (i = i0) → pB (t .fst) (t .snd) (t .snd) k
                  ; (i = i1) → pB (u .fst) (coe0→1 (λ k → B (p k .fst)) (t .snd)) (u .snd) k
                  ; (j = i1) → pB (p i .fst) (coe0→i (λ k → B (p k .fst)) i (t .snd)) (p i .snd) k })
         (coe0→i (λ x → B (p x .fst)) i (t .snd)))

isSetSndProp : (pB : (x : A) → isProp (B x)) (sA : (t u : Σ A B) → isProp (t .fst ≡ u .fst)) → isSet (Σ A B)
isSetSndProp pB sA t u =
  isPropRetract {A = t ≡ u}{fst t ≡ fst u} (cong fst) (congFst⁻ pB t u) (congFst⁻-congFst pB t u) (sA t u)

isGroupoidSndProp : (pB : (x : A) → isProp (B x)) → (sA : (t u : Σ A B) → isSet (t .fst ≡ u .fst)) → isGroupoid (Σ A B)
isGroupoidSndProp pB sA t u =
  isSetRetract {A = t ≡ u}{fst t ≡ fst u} (cong fst) (congFst⁻ pB t u) (congFst⁻-congFst pB t u) (sA t u)

is2GroupoidSndProp : (pB : (x : A) → isProp (B x)) → (sA : (t u : Σ A B) → isGroupoid (t .fst ≡ u .fst)) → is2Groupoid (Σ A B)
is2GroupoidSndProp pB sA t u = isGroupoidRetract {A = t ≡ u}{B = fst t ≡ fst u}
                                                 (cong fst) (congFst⁻ pB t u) (congFst⁻-congFst pB t u) (sA t u)

isSetΠ : ((x : A) → isSet (B x)) → isSet ((x : A) → B x)
isSetΠ h x y p q i j z = h z (x z) (y z) (λ k → p k z) (λ k → q k z)  i j

setPath : (A B : Type ℓ) (sB : isSet B) → isSet (A ≡ B)
setPath A B sB =
  isSetRetract {A = A ≡ B}{B = A ≃ B}
    (pathToEquiv {A = A}{B = B})
    (ua {A = A}{B})
    (ua-pathToEquiv {A = A}{B})
    (isSetSndProp {A = A → B}{B = isEquiv {A = A}{B}}
                  (isPropIsEquiv {A = A}{B = B})
                  (λ e1 e2 → isSetΠ {A = A}{B = λ _ → B} (λ _ → sB) (e1 .fst) (e2 .fst)))

isGroupoid-hSet : isGroupoid (hSet ℓ)
isGroupoid-hSet =
  isGroupoidSndProp {A = Type _}{B = isSet}
                    (λ A → isPropIsSet {A = A})
                    (λ t u → setPath (t .fst) (u .fst) (u .snd))


-- Next result
isGroupoidΠ : ((x : A) → isGroupoid (B x)) → isGroupoid ((x : A) → B x)
isGroupoidΠ h x y p q r s i j k z = h z (x z) (y z) (λ k → p k z) (λ k → q k z) (λ k l → r k l z) (λ k l → s k l z) i j k

groupoidPath : (A B : Type ℓ) (sB : isGroupoid B) → isGroupoid (A ≡ B)
groupoidPath A B sB =
  isGroupoidRetract {A = A ≡ B}{B = A ≃ B}
    (pathToEquiv {A = A}{B = B})
    (ua {A = A}{B = B})
    (ua-pathToEquiv {A = A}{B = B})
    (isGroupoidSndProp {A = A → B}{B = isEquiv}
       isPropIsEquiv
       (λ e1 e2 → isGroupoidΠ {A = A}{B = λ _ → B} (λ _ → sB) (e1 .fst) (e2 .fst)))

is2Groupoid-hGroupoid : is2Groupoid (hGroupoid ℓ)
is2Groupoid-hGroupoid =
  is2GroupoidSndProp {A = Type _}{B = isGroupoid}
    (λ A → isPropIsGroupoid {A = A})
    (λ t u → groupoidPath (t .fst) (u .fst) (u .snd))


--------------------------------------------------------------------------------
