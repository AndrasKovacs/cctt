
module Tests where

import MainInteraction

p1 = elabString $ unlines [
  ""
 -- ,"foo (A B : U)(p : A = B)(a : A) : coe 0 1 p a = coe 0 1 p a "
 -- ,"  := λ _. coe 0 1 (j.p j) a;"
  ,"transComp (A B : U) (p : A = B) (a : A) : a = coe 1 0 (j.p j) (coe 0 1 (j.p j) a)"
  ,"  := λ i. coe i 0 p (coe 0 i p a);"
  ]

p2 = elabString $ unlines [
   ""
  ,"id := (A : U) → A → A;"
  ,"Eq   : (A : U) → A → A → U := λ A x y. (P : A → U) → P x → P y;"
  ,"refl : (A : U)(x : A) → Eq A x x := λ A x P px. px;"
  ,"sym  : (A : U)(x y : A) → Eq A x y → Eq A y x := λ A x y p. p (λ y. Eq A y x) (refl A x) ;"
  ,"trs  : (A : U)(x y z : A) → Eq A x y → Eq A y z → Eq A x z := λ A x y z p q. q (λ z. Eq A x z) p;"
  ]

p3 = elabString $ unlines [
   ""
  ,"test2 : U := (A : U) × A;"
  ,"test3 : (x : (A : U) × A) → x.1 := λ x. x.2;"
  ,"test4 : (A : U) × A → U := λ _. U;"
  ,"test5 : (A : U)(B : A → U)(a : A)(b : B a) → (a : A) × B a := λ A B a b. (a, b);"
  ,"test6 : (A : U)(B : A → U)(x : (a : A) × B a) → A := λ A B x. x.1;"
  ,"test7 : (A : U)(B : A → U)(x : (a : A) × B a) → B x.1 := λ A B x. x.2;"

  ,"comtest (A B : U)(p : A = B)(x : A) : hcom 0 1 [] (coe 0 1 (i.p i) x) = com 0 1 (i. p i) [] x"
  ,"  := λ _. com 0 1 (i. p i) [] x;"

  ,"refl (A : U)(x : A) : x = x := λ _. x;"

  ,"trans (A : U)(x y z : A) (p : x = y) (q : y = z) : x = z"
  ,"  := λ i. hcom 0 1 [i=0 _. x; i=1 j. q j] (p i);"

  ,"sym (A : U)(x y : A) (p : x = y) : y = x "
  ,"  := λ i. hcom 0 1 [i=0 j. p j; i=1 _. x] x;"

  ,"ap (A B : U)(f : A → B)(x y : A)(p : x = y) : f x = f y"
  ,"   := λ i. f (p i);"

  ,"nestedlet  := let myid (A : U)(x : A) : A := x; myid;"
  ,"nestedlet2 : (A : U) → A → A := let myid (A : U)(x : A) : A := x; myid;"

  ,"testEta (A : U) (x y : A)(p : x = y) : p = p := refl (x = y) (λ i. p i);"

  ,"funext (A : U)(B : A → U)(f g : (a : A) → B a)(p : (a : A) → f a = g a) : f = g"
  ,"  := λ i a. p a i;"

  ,"coerce (A B : U) (p : A = B)(a : A) : B := coe 0 1 (i. p i) a;"

  ,"coerceinv (A B : U) (p : A = B)(b : B) : A := coe 1 0 (i. p i) b;"

  ,"subst (A : U)(P : A → U)(x y : A)(p : x = y)(px : P x) : P y := coe 0 1 (i. P (p i)) px;"

  ,"Sing (A : U) (a : A) : U := (x : A) × (a = x);"

  ,"connAnd (A : U)(a b : A)(p : a = b) : (λ _. a) ={i. a = p i} p"
  ,"  := let sq (l k : I) : A := hcom 1 l [k=0 _. a; k=1 x. p x] (p k);"
  ,""
  ,"     λ i j. hcom 0 1 [i=0 k. sq 0 k; i=1 k. sq j k;"
  ,"                      j=0 k. sq 0 k; j=1 k. sq i k;"
  ,"                      i=j k. sq i k] a;"

  ,"connAndDiag (A : U)(a b : A)(p : a = b) : p = (λ i. connAnd A a b p i i) := λ _. p;"

  ,"contractSing (A : U)(a b : A)(p : a = b) : (a, λ _. a) ={_. Sing A a} (b, p)"
  ,"  := λ i. (p i, connAnd A a b p i);"

  ,"Jbig (A : U)(a : A)(C : (x : A) → a = x → U)(cr : C a (refl A a))(x : A)(p : a = x) : C x p"
  ,"  := subst (Sing A a) (λ s. C s.1 s.2) (a, refl A a) (x, p) (contractSing A a x p) cr;"

  ,"J (A : U) (a : A) (C : (x : A) → a = x → U) (d : C a (λ _. a))(x : A) (p : a = x) : C x p"
  ,"  := let sq (i j : I) : A := hcom 0 j [i=0 _. a; i=1 x. p x] a;"
  ,"     coe 0 1 (i. C (sq i 1) (λ j. sq i j)) d;"

  ,"JEq (A : U) (a : A) (C : (x : A) → a = x → U) (d : C a (λ _. a))"
  ,"  : J A a C d a (λ _. a) = d"
  ,"  := let sq (i j : I) : A := hcom 0 j [i=0 _. a; i=1 _. a] a;"
  ,"     let cube (i j k : I) : A := hcom 0 j [k=0 x. sq i x;"
  ,"                                           k=1 _. a;"
  ,"                                           i=0 _. a;"
  ,"                                           i=1 _. a] a;"
  ,""
  ,"     λ k. com 0 1 (i. C (cube i 1 k) (λ j. cube i j k))"
  ,"                  [k=0 i. coe 0 i (i. C (sq i 1) (λ j. sq i j)) d;"
  ,"                   k=1 _. d]"
  ,"                  d;"

  ]
