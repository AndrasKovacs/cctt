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

  -- ,"refl : (A : U)(x : A) → x = x := λ A x _. x;"
  ,"trans : (A : U)(x y z : A) → x = y → y = z → x = z := "
  ,"  λ A x y z p q i. hcom 0 1 [i=0 _. x; i=1 j. q j] (p i);"
  ]

-- ("HCOMTOTAL",
--    "BindILazy {bindILazyName = \"_\", bindILazyBinds = 0, bindILazyBody = VNe (NLocalVar 1) []}"
--   ,"I1"
--   ,"VSub (VNe (NLocalVar 1) []) (0,1,[I1])")
