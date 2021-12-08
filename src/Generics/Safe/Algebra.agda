{-# OPTIONS --safe #-}

module Generics.Safe.Algebra where

open import Prelude
open import Generics.Safe.Description

private
  variable
    cb  : ConB
    cbs : ConBs

Algᶜ : {I : Set ℓⁱ} (D : ConD I cb) → (I → Set ℓ)
     → Set (ℓ ⊔ ℓⁱ ⊔ max-π cb ⊔ max-σ cb ⊔ hasRec? ℓ cb)
Algᶜ D X = ∀ {i} → ⟦ D ⟧ᶜ X i → X i

Algᶜˢ : {I : Set ℓⁱ} (Ds : ConDs I cbs) → (I → Set ℓ)
      → Set (ℓ ⊔ ℓⁱ ⊔ maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔
             hasCon? ℓⁱ cbs ⊔ maxMap (hasRec? ℓ) cbs)
Algᶜˢ D X = ∀ {i} → ⟦ D ⟧ᶜˢ X i → X i

Carrierᵖᵈ : (D : PDataD) (ℓ : Level) → Set (PDataD.plevel D ⊔ PDataD.ilevel D ⊔ lsuc ℓ)
Carrierᵖᵈ D ℓ = (p : ⟦ PDataD.Param D ⟧ᵗ) → ⟦ PDataD.Index D p ⟧ᵗ → Set ℓ

Algᵖᵈ : (D : PDataD) → Carrierᵖᵈ D ℓ
      → Set (ℓ ⊔ PDataD.plevel D ⊔ PDataD.ilevel D ⊔ PDataD.flevel D ℓ)
Algᵖᵈ D X = ∀ {p i} → ⟦ D ⟧ᵖᵈ p (X p) i → X p i

Carrierᵈ : (D : DataD) → (DataD.Levels D → Level) → Setω
Carrierᵈ D ℓf = (ℓs : DataD.Levels D) → Carrierᵖᵈ (DataD.applyL D ℓs) (ℓf ℓs)

Algᵈ : (D : DataD) {ℓf : DataD.Levels D → Level} → Carrierᵈ D ℓf → Setω
Algᵈ D {ℓf} X = ∀ {ℓs p i} → ⟦ D ⟧ᵈ ℓs p (X ℓs p) i → X ℓs p i
