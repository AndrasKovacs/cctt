{-# OPTIONS --cubical --type-in-type --postfix-projections --rewriting --show-irrelevant #-}

open import Cubical.Core.Everything hiding (Glue;glue;unglue)
-- import Cubical.Core.Everything as Cubical
open import Cubical.Foundations.Everything hiding (Glue;glue;unglue)
import Cubical.Foundations.Everything as Cubical

infix 3 _~>_
postulate _~>_ : {A : Type} → A → A → Type
{-# BUILTIN REWRITE _~>_ #-}

postulate
  Glue : ∀ (A : Type) {φ} → (Partial φ (Σ Type λ T → T ≃ A)) → Type

  glue : ∀ {A : Type} {φ : I}
         → {T : Partial  φ Type}
         → {e : PartialP φ (λ p → T p ≃ A)}
         → (t : PartialP φ T)
         → (a : Sub A φ (λ p → e p .fst (t p)))
         → Glue A (λ p → T p , e p)

  unglue :
       ∀ {A : Type} (φ : I) {T : Partial φ Type}
         {e : PartialP φ (λ p → T p ≃ A)}
       → Glue A (λ p → T p , e p)
       → A

postulate
  g1 : ∀ A Te → Glue A {i1} Te ~> Te 1=1 .fst
{-# REWRITE g1 #-}

postulate
  g2 : ∀ A T e t a → glue {A}{i1}{T}{e} t a ~> t 1=1
{-# REWRITE g2 #-}

postulate
  g3 : ∀ A T e g → unglue {A} i1 {T}{e} g ~> e 1=1 .fst g
{-# REWRITE g3 #-}

postulate
  g4 : ∀ A φ T e t a → unglue {A}φ {T}{e} (glue {A}{φ}{T}{e} t a) ~> outS a
{-# REWRITE g4 #-}

postulate
  g5 : ∀ A φ T e g → glue {A}{φ}{T}{e}(λ {(φ = i1) → g}) (inS (unglue {A} φ {T} {e} g))
                   ~> g
{-# REWRITE g5 #-}

extend' : ∀ {φ} {A : Type} → isContr A → (a : Partial φ A) → Sub A φ a
extend' {φ}{A} (a* , p) a = inS (hcomp (λ i → λ {(φ = i1) → p (a 1=1) i; (φ = i0) → a*}) a*)

-- weak Sub introduction
winS : ∀ {A : Type}{φ}(a : A)(a' : Partial φ A)(eq : PartialP φ λ p → a' p ≡ a)
       → Sub A (φ ∨ ~ φ) λ {(φ = i1) → a' 1=1; (φ = i0) → a}
winS {A} {φ} a a' eq = inS (hcomp (λ j → λ {(φ = i1) → eq 1=1 (~ j); (φ = i0) → a}) a)

-- glueToFib :
--          ∀ {A : Type} {φ : I}
--          → {T : Partial  φ Type}
--          → {e : PartialP φ (λ p → T p ≃ A)}
--          → (g : Glue A (λ p → T p , e p))
--          → (PartialP φ λ p → fiber (e p .fst) (unglue {A} φ {T} {e} g))
-- glueToFib {A} {φ} {T} {e} g p = {!g!} , {!!}

wglue : ∀ {A   : Type} {φ : I}
       → {T   : Partial  φ Type}
       → {e   : PartialP φ λ p → T p ≃ A}
       → (t   : PartialP φ T)
       → (a   : A)
       → (fib : PartialP φ λ p → e p .fst (t p) ≡ a)
       → Glue A (λ p → T p , e p)
wglue {A} {φ} {T} {e} t a fib =
  glue {A}{φ} {T}{e} t (inS (outS (winS a (λ .p → e p .fst (t p)) fib)))

-- doesn't work in Agda! I can't have Sub I

-- transpGlue :
--   ∀ (A  : I → Type)
--     (α  : I → I)
--     (Te : ∀ i → Partial (α i) (Σ Type λ T → T ≃ A i))
--   → (g : Glue (A i0) (Te i0))
--   → Glue (A i1) (Te i1)
-- transpGlue A α Te g = res where
--   a1 = transp A i0 (unglue (α i0) g)

--   t1 : PartialP (α i1) λ p → Te i1 p .fst
--   t1 = {!isContr!}

--   fib1 : PartialP (α i1) λ p → Te i1 p .snd .fst (t1 p) ≡ a1
--   fib1 = {!!}

--   res : Glue (A i1) (Te i1)
--   res = wglue {A i1}{α i1} t1 a1 fib1

{-

--------------------------------------------------------------------------------

Glue   : (A : Type) (α : I) (T : α=1 ⊢ Type) (f : α=1 ⊢ T ≃ A) → Type
glue   : (t : α=1 ⊢ T) → (a : A [α=1 ↦ f t]) → Glue A α T f
unglue : (g : Glue A α T f) → A

Glue A 1 T f = T
α=1 ⊢ glue t a = t
α=1 ⊢ unglue g = f g
unglue (glue t a) = a
glue [α=1 → g] (unglue {α} g) = g

i ⊢ A : Type    α : I  i, α=1 ⊢ A = A 0    a₀ : A 0
───────────────────────────────────────────────────────
        transpⁱ A α a₀ : A 1 [α=1 ↦ a₀]

A : Type   i, α=1 ⊢ a : A    a₀ : A[α=1 ↦ a 0]
──────────────────────────────────────────────
      hcompⁱ A a a₀ : A[α=1 ↦ a 1]

isContr : Type → Type
isContr A = (a* : A) × (∀ a → a* ≡ a)

fib : (A → B) → B → Type
fib f b = (a : A) × (f a ≡ b)

isEqv : (A → B) → Type
isEqv f = ∀ b → isContr (fib f b)

A ≃ B = (f : A → B) × isEqv f      -- we may write (f a) for application of equivalence

extend : (A : Type)(contr : isContr A)(a : α=1 ⊢ A) → A [α=1 ↦ a]
extend A (a*, p) a := hcompⁱ [α=1 → p a i] a*

wsub : (a : A)(a' : α=1 ⊢ A)(eq : α=1 ⊢ a' ≡ a) → A [α=1 ↦ a']
wsub a a' eq = hcompⁱ [α=i1 → eq (~ i)] a

wglue : (t : α=1 ⊢ T)(a : A)(eq : α=1 ⊢ f t ≡ a) → Glue A α T f
wglue t a eq = glue t (wsub a (f t) eq)

glueToFib : (g : Glue A α T f) → (α=1 ⊢ fib f (unglue g))
glueToFib g = (g, refl (unglue g))

--------------------------------------------------------------------------------


transpⁱ (Glue A α T f) β g : Glue (A 1) (α 1) (T 1) (f 1) [β=1 ↦ g]

  i, β=1 ⊢ Glue A α T f = Glue (A 0) (α 0) (T 0) (f 0)

  i : I ⊢ A : Type
        ⊢ α : I

  i : I, α=1 ⊢ T : Type
             ⊢ f : T ≃ A

  β : I

  g : Glue (A 0) (α 0) (T 0) (f 0)

  ASSUME:
    β = 1, i ⊢
      A i = A 0
      α i = α 0
      f i = f 0
      T i = T 0

  ------------------------------------------------------------

  1. transp the unglue

  a₁ : A 1 [β=1 → unglue g]
  a₁ = transpⁱ A β (unglue g)

  2. get a partial fiber at 1

  fib₁ : (α 1) = 1 ⊢ (β = 1 ⊢ fib (f 1) a₁)
  fib₁ = [β=1 ↦ glueToFib g]

  3. extend to total

  (t, p) : α 1 = 1 ⊢ fib (f 1) a₁
  (t, p) = extend (fib (f 1) a₁) (f 1 .isEquiv a₁) fib₁

  g₁ : Glue (A 1) (α 1) (T 1) (f 1)
  g₁ = wglue t a₁ p


  -- inlined incoherent transp
  ------------------------------------------------------------

  itranspⁱ (Glue A α T f) β g :=

    a₁ : A 1 [β=1 → unglue g]
    a₁ = transpⁱ A β (unglue g)

    (fib*, contr) : α 1 = 1 ⊢ isContr (fib (f 1) a₁)
    (fib*, contr) = f 1 .isEquiv a₁

    (t, f1t≡a₁) : α 1 = 1 ⊢ fib (f 1) a₁
    (t, f1t≡a₁) = hcompʲ [β=1 ↦ contr (g, refl (unglue g)) j] fib*

    g₁ : Glue (A 1) (α 1) (T 1) (f 1)
    g₁ = glue t (hcompʲ [α 1 = 1 → f1t≡a₁ (~j), β=1 → a₁] a₁)

       α 1 = 1, β = 1 ⊢
          a₁ = unglue g

          f1t≡a₁ ~j = contr (g, refl (unglue g)) 1 .snd ~j
                    = (g, refl (unglue g)) .snd ~j
                    = (refl (unglue g)) ~j
                    = unglue g OK

      β = 1 ⊢ t = g OK

     itranspⁱ (Glue A α T f) β g : (Glue A1 α1 T1 f1)[β=1 ↦ g]

  -- coherent transp from hcomp. Needs hcomp for Glue, probably not
  -- very efficient, but at least it's easy to write and understand!

  transpⁱ (Glue A α T f) β g =
    hcompⁱ [β ↦ g, ∀i.α → transpFillⁱ T β g] (itranspⁱ A α T f β g)

      -- doesn't work just like this!

      ∀i.α ⊢ transpFillⁱ T β g = itranspⁱ A α T f β g
                               = t
                               = fst (hcompʲ [β ↦ contr (g, refl (unglue g)) j] fib*)

-- hcomp for glue
--------------------------------------------------------------------------------

  assume
    g₀ : Glue A α T f
    i, β ⊢ t : Glue A α T f
    β ⊢ t 0 = g₀

hcompⁱ (Glue A α T f) [β ↦ g] g₀ : Glue A α T f [β ↦ t 1]

  a₁ : A
  a₁ := hcompⁱ A [β ↦ unglue g, α ↦ f (hfillⁱ T [β ↦ g] g₀)] (unglue g₀)

  g₁ := glue [α ↦ hcompⁱ T [β → g] g₀] a₁

     α ⊢ hcompⁱ T [β → g] g₀ : T
       ⊢ a₁ = f (hcompⁱ T [β → g] g₀)  OK! + coherence

  in short:

  := glue [α ↦ hcompⁱ T [β → g] g₀]
          (hcompⁱ A [β ↦ unglue g, α ↦ f (hfillⁱ T [β ↦ g] g₀)] (unglue g₀))


-- CCHM comp
--------------------------------------------------------------------------------

icompⁱ (Glue [α ↦ (T, f)] A) [β ↦ g] g₀

  a₁ : A 1
  a₁ := compⁱ A [β ↦ unglue g] (unglue g₀)

  (fib*, contr) : α1 ⊢ isContr (fib f1 a₁)
  (fib*, contr) = f1 .isEquiv a₁

  (t, f1t≡a₁) : α1 ⊢ fib f1 a₁
  (t, f1t≡a₁) = hcompⁱ [β ↦ contr (g1, refl (f1 g1)) i] fib*

  g₁ : Glue A1 α1 T1 f1
  g₁ = glue [α1 ↦ t] (hcompⁱ [α1 → f1t≡a₁ (~i), β → unglue g1] a₁)


  compⁱ (Glue [α ↦ (T, f)] A) [β ↦ g] g₀ =
    icompⁱ α T f A [β ↦ gi, ∀i.α ↦ fillⁱ T [β ↦ g] g₀] g₀


-- Cartesian coe
--------------------------------------------------------------------------------

icoe i:r~>r' (Glue [α ↦ (T, f)] A) g₀ : Glue [αr' ↦ (Tr', fr')] Ar' [r=r' ↦ g₀]

   ar' : A r'
   ar' = coe i r r' (unglue g₀)

   (fib*, contr) : αr' ⊢ isContr (fib fr' ar')
   (fib*, contr) = fr' .isEquiv ar'

   (t, fr't=ar') : αr' ⊢ fib fr' ar'
   (t, fr't=ar') = hcomp j 0 1 [r=r' ↦ contr (g₀, refl (fr g₀)) j] fib*

   g₁ : Glue [αr' ↦ (Tr', fr')] Ar'
   g₁ = glue [αr' ↦ t] (hcomⁱ 1 0 [αr' ↦ fr't=ar' i] ar')


   ∀i.α ⊢ g₁ = coeⁱ r r' T g₀
        ⊢ t  = coeⁱ r r' T g₀

          t = fst (hcomp j 0 1 [r=r' ↦ contr (g₀, refl (fr g₀)) j] fib*)


   coeⁱ r r' (Glue [α ↦ (T, f)] A) g₀ :=
     hcomʲ 0 1 [      (icoeⁱ r r' (Glue [α ↦ (T, f)] A) g₀)


icoe i:r~>r' (Glue [α ↦ (T, f)] A) g₀ : Glue [αr' ↦ (Tr', fr')] Ar' [r=r' ↦ g₀]

   ar' : A r'
   ar' = coe i r r' (unglue g₀)

   (fib*, contr) : αr' ⊢ isContr (fib fr' ar')
   (fib*, contr) = fr' .isEquiv ar'

   (t, fr't=ar') : αr' ⊢ fib fr' ar'
   (t, fr't=ar') = hcomp j 0 1 [
      r=r' ↦ contr (g₀, refl (fr g₀)) j
    , ∀i.α ↦ contr (coeⁱ r r' T g₀, ?) j]    ? : fr' (coeⁱ r r' T g₀) = coeⁱ r r' T (fr g₀)
      fib*

       ? : fr' (coeⁱ r r' T g₀) ≡ coeⁱ r r' T (fr g₀)

          λ j. hcomʲ [j=0 ↦ fr' (coeⁱ r r' T g₀), j=1 ↦ coeⁱ r r' T (fr g₀)]






   g₁ : Glue [αr' ↦ (Tr', fr')] Ar'
   g₁ = glue [αr' ↦ t] (hcomⁱ 1 0 [αr' ↦ fr't=ar' i] ar')


   ∀i.α ⊢ g₁ = coeⁱ r r' T g₀
        ⊢ t  = coeⁱ r r' T g₀

          t = fst (hcomp j 0 1 [r=r' ↦ contr (g₀, refl (fr g₀)) j] fib*)


   coeⁱ r r' (Glue [α ↦ (T, f)] A) g₀ :=
     hcomʲ 0 1 [      (icoeⁱ r r' (Glue [α ↦ (T, f)] A) g₀)


LEMMA
  i ⊢ A
  a : A r
  coeⁱ r r' A a : A r' [r=r' ↦ a]


  j ⊢ coeⁱ r j A a : A j [j=r ↦ a, j=r' ↦ coeⁱ r r' A a]

  j ⊢ coeⁱ r j (A i) a


    Pathʲ (A j) a


CARTESIAN comp

icompⁱ r r' (Glue [α ↦ (T, f)] A) [β ↦ t] gr

  ar' := compⁱ r r' [β ↦ unglue t] (unglue gr)

  (fib*, contr) : αr' ⊢ isContr (fib fr' ar')
  (fib*, contr) = fr' .isEquiv ar'

  (topt, fr'topt≡ar') : αr' ⊢ fib fr' ar'
  (topt, fr'topt≡ar') = hcompⁱ 0 1
    [β ↦ contr (tr', refl (fr' tr')) i, r=r' ↦ contr (gr, refl (fr gr)) i] fib*

  Res = glue [αr' ↦ topt] (hcompⁱ 1 0 [αr' ↦ fr'topt≡ar' i, β ↦ unglue tr', r=r' ↦ unglue gr] ar')

  compⁱ r r' (Glue [α ↦ (T, f)] A) [β ↦ t] gr
    = icompⁱ r r' (Glue [α ↦ (T, f)] A) [β ↦ t, ∀i.α ↦ fillⁱ r r' [β ↦ g] gr] gr


CARTESIAN comp inline

compⁱ r r' (Glue [α ↦ (T, f)] A) [β ↦ t] gr

  ar = unglue gr

  ar' := compⁱ r r' [β ↦ unglue t, ∀i.α ↦ fillⁱ r r' [β ↦ unglue t] ar)] ar

  (fib*, contr) : αr' ⊢ isContr (fib fr' ar')
  (fib*, contr) = fr' .isEquiv ar'

  (topt, fr'topt≡ar') : αr' ⊢ fib fr' ar'
  (topt, fr'topt≡ar') = hcompⁱ 0 1
    [β    ↦ contr (tr', refl (fr' tr')) i,
     ∀i.α ↦ contr (compⁱ r r' [β ↦ t] gr, refl _) i
     r=r' ↦ contr (gr, refl (fr gr)) i] fib*

  Res = glue [αr' ↦ topt]
             (hcompⁱ 1 0 [
                αr'  ↦ fr'topt≡ar' i,
                β    ↦ unglue tr',
                ∀i.α ↦ compⁱ r r' [β ↦ unglue t] ar
                r=r' ↦ unglue gr ]
                ar')


CARTESIAN coe

coeⁱ r r' (Glue [α ↦ (T, f)] A) gr :=
  compⁱ r r' (Glue [α ↦ (T, f)] A) [] gr



coeⁱ r r' (Glue [α ↦ (T, f)] A) gr

  ar := unglue gr

  ar' := compⁱ r r' A [∀i.α ↦ coefillⁱ r r' A ar] ar

  (fib*, contr) : αr' ⊢ isContr (fib fr' ar')
  (fib*, contr) = fr' .isEquiv ar'

  (topt, fr'topt≡ar') : αr' ⊢ fib fr' ar'
  (topt, fr'topt≡ar') = hcompⁱ 0 1
    [∀i.α ↦ contr (coeⁱ r r' T gr, refl _) i, r=r' ↦ contr (gr, refl (fr gr)) i] fib*

  Res = glue [αr' ↦ topt]
             (hcompⁱ 1 0 [αr' ↦ fr'topt≡ar' i, ∀i.α ↦ coeⁱ r r' A ar, r=r' ↦ unglue gr] ar')


CARTESIAN coe UA

ua (f : A≃B) = λ i. Glue [i=0 ↦ (A, f), i=1 ↦ (B, idEqv)] B

coeⁱ 0 1 (ua f) : A → B

coeⁱ 0 1 (Glue [(i=0)∨(i=1) ↦ (T, f)] A) gr

  Res = hcompⁱ 0 1 [] (hcompⁱ 0 1 [] (f gr))


CARTESIAN hcomp

hcompⁱ r r' (Glue [α ↦ (T, f)] A) [β ↦ t] gr : Glue [α ↦ (T, f)] A [β ↦ tr']

  glue [α ↦ hcompⁱ r r' T [β ↦ t] gr]
       (hcompⁱ r r' A [β ↦ unlgue t, α ↦ f (hfillⁱ r r' T [β ↦ t] gr)] (unglue gr))




SYM

p : Path A x y

λ i. hcompʲ 1 0 A [i=0 ↦ y, i=1 ↦ p j] y


compⁱ r r' A [β ↦ t] a := hcompⁱ r r' (A r') [β ↦ coefill⁻¹ i r r' A t] (coeⁱ r r' A a)


hcompⁱ r r' ((x:A)×B x) [β ↦ t] b =
   ( hcompⁱ r r' A [β ↦ t.1](b.1)
   , compⁱ  r r' (B (hfill i r r' A [β ↦ t.1] (b.1))) [β ↦ t.2] b.2 )




-}
