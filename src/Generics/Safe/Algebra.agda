{-# OPTIONS --safe --without-K #-}

module Generics.Safe.Algebra where

open import Prelude
open import Generics.Safe.Telescope
open import Generics.Safe.Description

private variable
  rb  : RecB
  cb  : ConB
  cbs : ConBs

Carrierᶜ : {I : Set ℓⁱ} → ConD I cb → (ℓ : Level) → Set _
Carrierᶜ {I = I} _ ℓ = I → Set ℓ

Algᶜ : {I : Set ℓⁱ} (D : ConD I cb) → Carrierᶜ D ℓ → Set _
Algᶜ D X = ∀ {i} → ⟦ D ⟧ᶜ X i → X i

Carrierᶜˢ : {I : Set ℓⁱ} → ConDs I cbs → (ℓ : Level) → Set _
Carrierᶜˢ {I = I} _ ℓ = I → Set ℓ

Algᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) → Carrierᶜˢ D ℓ → Set _
Algᶜˢ D X = ∀ {i} → ⟦ D ⟧ᶜˢ X i → X i

Carrierᵖᵈ : (D : PDataD) (ℓ : Level) → Set _
Carrierᵖᵈ D ℓ = (ps : ⟦ PDataD.Param D ⟧ᵗ) → Carrierᶜˢ (PDataD.applyP D ps) ℓ

Algᵖᵈ : (D : PDataD) → Carrierᵖᵈ D ℓ → Set _
Algᵖᵈ D X = ∀ {ps is} → ⟦ D ⟧ᵖᵈ (X ps) is → X ps is

Carrierᵈ : (D : DataD) → (DataD.Levels D → Level) → Setω
Carrierᵈ D ℓf = (ℓs : DataD.Levels D) → Carrierᵖᵈ (DataD.applyL D ℓs) (ℓf ℓs)

Algᵈ : (D : DataD) {ℓf : DataD.Levels D → Level} → Carrierᵈ D ℓf → Setω
Algᵈ D X = ∀ {ℓs p i} → ⟦ D ⟧ᵈ (X ℓs p) i → X ℓs p i

record Algebraᵖᵈ (D : PDataD) ps ℓ
     : let ℓⁱ  = PDataD.ilevel D
           cbs = PDataD.struct D
       in  Set (ℓⁱ ⊔ maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ maxMap (hasRec? ℓ) cbs ⊔
                hasCon? ℓⁱ cbs ⊔ lsuc ℓ) where
  constructor algebra
  field
    Carrier : Carrierᶜˢ (PDataD.applyP D ps) ℓ
    apply   : Algᶜˢ (PDataD.applyP D ps) Carrier

Algebraᵈ : ∀ (D : DataD) ℓs ps ℓ → Set _
Algebraᵈ D ℓs = Algebraᵖᵈ (DataD.applyL D ℓs)

Coalgᵈ : (D : DataD) {ℓf : DataD.Levels D → Level} → Carrierᵈ D ℓf → Setω
Coalgᵈ D X = ∀ {ℓs p i} → X ℓs p i → ⟦ D ⟧ᵈ (X ℓs p) i
