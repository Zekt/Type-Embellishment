{-# OPTIONS --without-K --safe #-}

module Prelude.Level where

open import Agda.Primitive                public
  using    (Level; _⊔_; Setω; lzero; lsuc)

open import Agda.Builtin.Nat
  renaming (Nat to ℕ)
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

variable
  ℓ ℓ' ℓ'' ℓ′ ℓᵉ ℓⁱ ℓʲ ℓᵏ ℓˣ ℓʸ : Level

-- Lifting.

record Lift {a} ℓ (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A

open Lift public

-- Synonyms

0ℓ 1ℓ 2ℓ : Level
0ℓ = lzero
1ℓ = lsuc 0ℓ
2ℓ = lsuc 1ℓ

rewriteLevel : ∀ {ℓ ℓ'} → ℓ ≡ ℓ' → Set ℓ → Set ℓ'
rewriteLevel refl X = X

infix 4 _⊑_ -- Type `\squb=` to get `⊑`
_⊑_ : Level → Level → Set
ℓ₁ ⊑ ℓ₂ = ℓ₁ ⊔ ℓ₂ ≡ ℓ₂

levelOfType : ∀ {a} → Set a → Level
levelOfType {a} _ = a

levelOfTerm : ∀ {a} {A : Set a} → A → Level
levelOfTerm {a} _ = a
