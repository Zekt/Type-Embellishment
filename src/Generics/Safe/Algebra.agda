{-# OPTIONS --safe #-}

module Generics.Safe.Algebra where

open import Prelude
open import Generics.Safe.Description

private
  variable
    cb : ConB
    cbs : ConBs

Algᶜ : {I : Set ℓⁱ} (D : ConD I cb) → (I → Set ℓ)
     → Set (ℓ ⊔ ℓⁱ ⊔ max-π cb ⊔ max-σ cb ⊔ hasRec? ℓ cb)
Algᶜ D X = ∀ {i} → ⟦ D ⟧ᶜ X i → X i

Algᶜˢ : {I : Set ℓⁱ} (Ds : ConDs I cbs) → (I → Set ℓ)
      → Set (ℓ ⊔ ℓⁱ ⊔ maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔
             hasCon? ℓⁱ cbs ⊔ maxMap (hasRec? ℓ) cbs)
Algᶜˢ D X = ∀ {i} → ⟦ D ⟧ᶜˢ X i → X i

Carrierᵈ : (D : DataD) (ℓ : Level) → Set (DataD.plevel D ⊔ DataD.ilevel D ⊔ lsuc ℓ)
Carrierᵈ D ℓ = (p : ⟦ DataD.Param D ⟧ᵗ) → ⟦ DataD.Index D p ⟧ᵗ → Set ℓ

Algᵈ : (D : DataD) → Carrierᵈ D ℓ
     → Set (ℓ ⊔ DataD.plevel D ⊔ DataD.ilevel D ⊔ DataD.flevel D ℓ)
Algᵈ D X = ∀ {p i} → ⟦ D ⟧ᵈ p (X p) i → X p i

Carrierᵘᵖᵈ : (D : UPDataD) → (UPDataD.Levels D → Level) → Setω
Carrierᵘᵖᵈ D ℓf = (ℓs : UPDataD.Levels D) → Carrierᵈ (UPDataD.Desc D ℓs) (ℓf ℓs)

Algᵘᵖᵈ : (D : UPDataD) {ℓf : UPDataD.Levels D → Level} → Carrierᵘᵖᵈ D ℓf → Setω
Algᵘᵖᵈ D {ℓf} X = ∀ {ℓs p i} → ⟦ D ⟧ᵘᵖᵈ ℓs p (X ℓs p) i → X ℓs p i
