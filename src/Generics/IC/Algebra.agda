{-# OPTIONS --safe #-}

module Generics.IC.Algebra where

open import Agda.Primitive
open import Agda.Builtin.Sigma

open import Generics.IC.Description

Carrier : ∀ {ℓᵖ ℓⁱ} (P : Tel₀ ℓᵖ) → Tel ⟦ P ⟧ᵗ⁰ ℓⁱ → ⟦ P ⟧ᵗ⁰ → Set (lsuc ℓⁱ)
Carrier {_} {ℓⁱ} P I p = ⟦ I ⟧ᵗ p → Set ℓⁱ

module _ {ℓᵖ ℓⁱ} {P : Tel₀ ℓᵖ} {I : Tel ⟦ P ⟧ᵗ⁰ ℓⁱ}
         (D : SetD P I) (p : ⟦ P ⟧ᵗ⁰) (X : Carrier P I p) where

  record Alg : Set (lsuc ℓⁱ) where
    constructor algebra
    field
      apply : {i : ⟦ I ⟧ᵗ p} → ⟦ D ⟧ˢ p X i → X i

  record Coalg : Set (lsuc ℓⁱ) where
    constructor coalgebra
    field
      apply : {i : ⟦ I ⟧ᵗ p} → X i → ⟦ D ⟧ˢ p X i