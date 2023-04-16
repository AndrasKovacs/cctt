{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything

data Bool : Set where
  true false : Bool

not : Bool → Bool
not true  = false
not false = true

notIso : Iso Bool Bool
Iso.fun      notIso b     = not b
Iso.inv      notIso b     = not b
Iso.rightInv notIso true  = refl
Iso.rightInv notIso false = refl
Iso.leftInv  notIso true  = refl
Iso.leftInv  notIso false = refl

notPath : Bool ≡ Bool
notPath = isoToPath notIso

bigPath =
    notPath ∙ notPath ∙ notPath ∙ notPath ∙ notPath ∙ notPath
  ∙ notPath ∙ notPath ∙ notPath ∙ notPath ∙ notPath ∙ notPath

test : Bool
test = transport bigPath true
