{-# OPTIONS --safe --without-K #-}

module Generics.Safe.Algebra where

open import Prelude
open import Generics.Safe.Description

private
  variable
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
Carrierᵖᵈ D ℓ = (p : ⟦ PDataD.Param D ⟧ᵗ) → Carrierᶜˢ (PDataD.applyP D p) ℓ

Algᵖᵈ : (D : PDataD) → Carrierᵖᵈ D ℓ → Set _
Algᵖᵈ D X = ∀ {p i} → ⟦ D ⟧ᵖᵈ p (X p) i → X p i

Carrierᵈ : (D : DataD) → (DataD.Levels D → Level) → Setω
Carrierᵈ D ℓf = (ℓs : DataD.Levels D) → Carrierᵖᵈ (DataD.applyL D ℓs) (ℓf ℓs)

Algᵈ : (D : DataD) {ℓf : DataD.Levels D → Level} → Carrierᵈ D ℓf → Setω
Algᵈ D X = ∀ {ℓs p i} → ⟦ D ⟧ᵈ ℓs p (X ℓs p) i → X ℓs p i

record Alg (D : DataD) : Setω where
  field
    {flevel} : DataD.Levels D → Level
    Carrier  : Carrierᵈ D flevel
    apply    : Algᵈ D Carrier

Coalgᵈ : (D : DataD) {ℓf : DataD.Levels D → Level} → Carrierᵈ D ℓf → Setω
Coalgᵈ D X = ∀ {ℓs p i} → X ℓs p i → ⟦ D ⟧ᵈ ℓs p (X ℓs p) i
