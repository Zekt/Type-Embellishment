open import Prelude
open import Generics.Description

module Utils.Telescope where

--mutual
--  append : ∀ {ℓ ℓᵇ} {B : Set ℓᵇ} → Tel B ℓ → Tel B ℓ → Tel B ℓ
--  append tel₁ nil = tel₁
--  append tel₁ (snoc tel₂ A) = snoc (append tel₁ tel₂) λ { (b , btel) → A (b , shrink btel)}
--
--  shrink : ∀ {ℓ ℓᵇ} {B : Set ℓᵇ} {b : B} {tel₁ tel₂ : Tel B ℓ} → ⟦ append tel₁ tel₂ ⟧ᵗ b → ⟦ tel₂ ⟧ᵗ b
--  shrink {tel₁ = tel₁} {tel₂ = nil} tel = tt
--  shrink {tel₁ = tel₁} {tel₂ = snoc tel₂ A} (tel , typ) = (shrink tel) , typ
