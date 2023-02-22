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
  ,"mycoe : (A B : U) → A = B → A → B := λ A B p x. coe 0 1 i (p i) x;"
  ,"x := suc (suc zero);"
  ,"test := hcom 0 1 [] zero;"
  ]
