{-# OPTIONS --safe #-}

module Prelude.Level where

open import Agda.Primitive                public
  using    (Level; _⊔_; Setω; lzero; lsuc)

open import Agda.Builtin.Nat
  renaming (Nat to ℕ)
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

variable
  ℓ ℓ' ℓ'' ℓ′ ℓⁱ ℓʲ ℓᵏ ℓˣ ℓʸ : Level

-- Lifting.

record Lift {a} ℓ (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A

open Lift public

-- Synonyms

0ℓ : Level
0ℓ = lzero

_^_ : Set → ℕ → Set
A ^ zero  = ⊤
A ^ suc n = Σ A λ _ → A ^ n

rewriteLevel : ∀ {ℓ ℓ'} → ℓ ≡ ℓ' → Set ℓ → Set ℓ'
rewriteLevel refl X = X
