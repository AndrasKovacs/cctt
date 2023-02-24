{-# options_ghc -Wno-unused-imports #-}

module Main where

import Common
import Elaboration
import Parser
import Pretty


main :: IO ()
main = putStrLn "hello"

-- | Elaborate a string, render output.
justElab :: String -> IO ()
justElab str = do
  top <- parseString "(interactive)" str
  top <- elabTop "(interactive)" str top
  putStrLn $ showTop top

--------------------------------------------------------------------------------

p1 = justElab $ unlines [
   ""
  ,"id : (A : U) → A → A → A := λ A x y. z;"
  ]

p2 = justElab $ unlines [
   ""
  ,"id := (A : U) → A → A;"
  ,"Eq   : (A : U) → A → A → U := λ A x y. (P : A → U) → P x → P y;"
  ,"refl : (A : U)(x : A) → Eq A x x := λ A x P px. px;"
  ,"sym  : (A : U)(x y : A) → Eq A x y → Eq A y x := λ A x y p. p (λ y. Eq A y x) (refl A x) ;"
  ,"trs  : (A : U)(x y z : A) → Eq A x y → Eq A y z → Eq A x z := λ A x y z p q. q (λ z. Eq A x z) p;"
  ]

p3 = justElab $ unlines [
   ""
  -- ,"test2 : U := (A : U) × A;"
  -- ,"test3 : (x : (A : U) × A) → x.1 := λ x. x.2;"
  -- ,"test4 : (A : U) × A → U := λ _. U;"
  -- ,"test5 : (A : U)(B : A → U)(a : A)(b : B a) → (a : A) × B a := λ A B a b. (a, b);"
  -- ,"test6 : (A : U)(B : A → U)(x : (a : A) × B a) → A := λ A B x. x.1;"
  -- ,"test7 : (A : U)(B : A → U)(x : (a : A) × B a) → B x.1 := λ A B x. x.2;"

  -- ,"refl (A : U)(x : A) : x = x := λ _. x;"

  -- ,"trans (A : U)(x y z : A) (p : x = y) (q : y = z) : x = z"
  -- ,"  := λ i. hcom 0 1 [i=0 _. x; i=1 j. q j] (p i);"

  -- ,"sym (A : U)(x y : A) (p : x = y) : y = x "
  -- ,"  := λ i. hcom 0 1 [i=0 j. p j; i=1 _. x] x;"

  -- ,"ap (A B : U)(f : A → B)(x y : A)(p : x = y) : f x = f y"
  -- ,"   := λ i. f (p i);"

  ,"foo : (A : U) → A → A := let myid : (A : U) → A → A := λ A x. x; myid;"

  ]

-- testEta (A : U) (a b : A) (p : Path A a b) : Path (Path A a b) p p = refl (Path A a b) (<i> p @ i)
