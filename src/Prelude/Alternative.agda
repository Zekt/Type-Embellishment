{-# OPTIONS --without-K --safe #-}

module Prelude.Alternative where

open import Agda.Primitive
open import Agda.Builtin.Bool

open import Prelude.Functor

private variable
  A B : Set _

record FunctorZero (F : ∀ {ℓ} → Set ℓ → Set ℓ) : Setω where
  field
    empty : F A
    overlap {{super}} : Functor F

record Alternative (F : ∀ {ℓ} → Set ℓ → Set ℓ) : Setω where
  infixl 3 _<|>_
  field
    _<|>_ : F A → F A → F A
    overlap {{super}} : FunctorZero F

open FunctorZero ⦃...⦄ public
open Alternative ⦃...⦄ public

{-# DISPLAY FunctorZero.empty _     = empty   #-}
{-# DISPLAY Alternative._<|>_ _ x y = x <|> y #-}

module _ {F : ∀ {ℓ} → Set ℓ → Set ℓ} ⦃ _ : FunctorZero F ⦄ where
  guard : Bool → F A → F A
  guard true  x = x
  guard false _ = empty
