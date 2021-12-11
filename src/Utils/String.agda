{-# OPTIONS --safe --without-K #-}

open import Prelude as P
  hiding (concat; intersperse)

module Utils.String where

concat : List String → String
concat = foldr "" _<>_

intersperse : String → List String → String
intersperse sep = concat ∘ P.intersperse sep
