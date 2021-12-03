{-# OPTIONS --safe #-}

module Generics.Safe.Algebra where

open import Prelude
open import Generics.Safe.Description

private
  variable
    ℓ ℓⁱ ℓᵃ : Level
    cρ : ℕ
    cρs : List ℕ

Algᶜ : {I : Set ℓⁱ} (D : ConD I ℓᵃ cρ) → (I → Set ℓ)
     → Set (ℓⁱ ⊔ ℓᵃ ⊔ ℓ ⊔ lcond cρ ℓ)
Algᶜ D X = ∀ {i} → ⟦ D ⟧ᶜ X i → X i

Algᶜˢ : {I : Set ℓⁱ} (Ds : ConDs I ℓᵃ cρs) → (I → Set ℓ)
      → Set (ℓⁱ ⊔ ℓᵃ ⊔ ℓ ⊔ lcond (length cρs) ℓⁱ ⊔ lconds cρs ℓ)
Algᶜˢ D X = ∀ {i} → ⟦ D ⟧ᶜˢ X i → X i

Carrierᵈ : (D : DataD) (ℓ : Level) → Set (DataD.plevel D ⊔ DataD.ilevel D ⊔ lsuc ℓ)
Carrierᵈ D ℓ = (p : ⟦ DataD.Param D ⟧ᵗ) → ⟦ DataD.Index D p ⟧ᵗ → Set ℓ

Algᵈ : (D : DataD) → Carrierᵈ D ℓ
     → Set (ℓ ⊔ DataD.plevel D ⊔ DataD.ilevel D ⊔ DataD.alevel D
              ⊔ lcond (length (DataD.recCounts D)) (DataD.ilevel D)
              ⊔ lconds (DataD.recCounts D) ℓ)
Algᵈ D X = ∀ {p i} → ⟦ D ⟧ᵈ p (X p) i → X p i

Carrierᵘᵖᵈ : (D : UPDataD) (ℓ : Level) → Setω
Carrierᵘᵖᵈ D ℓ = (ℓs : UPDataD.Levels D) → Carrierᵈ (UPDataD.Desc D ℓs) ℓ

Algᵘᵖᵈ : (D : UPDataD) → Carrierᵘᵖᵈ D ℓ → Setω
Algᵘᵖᵈ D X = ∀ {ℓs p i} → ⟦ D ⟧ᵘᵖᵈ ℓs p (X ℓs p) i → X ℓs p i