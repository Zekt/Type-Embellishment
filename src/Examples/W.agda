{-# OPTIONS --safe --with-K #-}

module Examples.W where

open import Prelude
open import Generics.Telescope
open import Generics.Description
open import Generics.Ornament.Description
open import Generics.Ornament.Algebraic
open import Generics.SimpleContainer

open import Generics.Reflection

data W {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  sup : (a : A) → (B a → W A B) → W A B
