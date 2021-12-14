{-# OPTIONS --safe --without-K #-}

module Prelude.Coercion where

open import Prelude.Level

record Coercion (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  field
    ⇑_ : (x : A) → B x

  
open Coercion ⦃...⦄ public

Coercion' : (A : Set ℓ) → (B : Set ℓ') → Set (ℓ ⊔ ℓ')
Coercion' A B = Coercion A λ _ → B

coerce_to_ : {A : Set ℓ} → (x : A) → (B : A → Set ℓ') → ⦃ _ : Coercion A B ⦄ → B x
coerce x to B = ⇑ x

coerce'_to_ : {A : Set ℓ} → (x : A) → (B : Set ℓ') → ⦃ _ : Coercion' A B ⦄ → B
coerce' x to B = ⇑ x
