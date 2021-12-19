{-# OPTIONS --safe --without-K #-}

module Generics.Safe.Algebra where

open import Prelude
open import Generics.Safe.Description

private variable
  rb  : RecB
  cb  : ConB
  cbs : ConBs

Carrierᶜ : {I : Set ℓⁱ} → ConD I cb → (ℓ : Level) → Set _
Carrierᶜ {I = I} _ ℓ = I → Set ℓ

Carrierᶜˢ : {I : Set ℓⁱ} → ConDs I cbs → (ℓ : Level) → Set _
Carrierᶜˢ {I = I} _ ℓ = I → Set ℓ

Carrierᵖᵈ : ∀ (D : PDataD) ps ℓ → Set _
Carrierᵖᵈ D ps ℓ = Carrierᶜˢ (PDataD.applyP D ps) ℓ

Carrierᵈ : ∀ (D : DataD) ℓs ps ℓ → Set _
Carrierᵈ D ℓs = Carrierᵖᵈ (DataD.applyL D ℓs)

Algᶜ : {I : Set ℓⁱ} (D : ConD I cb) → Carrierᶜ D ℓ → Set _
Algᶜ D X = ∀ {i} → ⟦ D ⟧ᶜ X i → X i

Algᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) → Carrierᶜˢ D ℓ → Set _
Algᶜˢ D X = ∀ {i} → ⟦ D ⟧ᶜˢ X i → X i

Algᵖᵈ : ∀ (D : PDataD) {ps} → Carrierᵖᵈ D ps ℓ → Set _
Algᵖᵈ D X = ∀ {is} → ⟦ D ⟧ᵖᵈ X is → X is

Algᵈ : ∀ (D : DataD) {ℓs ps} → Carrierᵈ D ℓs ps ℓ → Set _
Algᵈ D X = ∀ {is} → ⟦ D ⟧ᵈ X is → X is

record Algebra {I : Set ℓⁱ} (D : ConDs I cbs) ℓ
     : Set (ℓⁱ ⊔ maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ maxMap (hasRec? ℓ) cbs ⊔
            hasCon? ℓⁱ cbs ⊔ lsuc ℓ) where
  constructor algebra
  field
    Carrier : Carrierᶜˢ D ℓ
    apply   : Algᶜˢ D Carrier

Algebraᵖᵈ : ∀ (D : PDataD) ps ℓ → Set _
Algebraᵖᵈ D ps = Algebra (PDataD.applyP D ps)

Algebraᵈ : ∀ (D : DataD) ℓs ps ℓ → Set _
Algebraᵈ D ℓs = Algebraᵖᵈ (DataD.applyL D ℓs)

Coalgᶜ : {I : Set ℓⁱ} (D : ConD I cb) → Carrierᶜ D ℓ → Set _
Coalgᶜ D X = ∀ {i} → X i → ⟦ D ⟧ᶜ X i

Coalgᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) → Carrierᶜˢ D ℓ → Set _
Coalgᶜˢ D X = ∀ {i} → X i → ⟦ D ⟧ᶜˢ X i

Coalgᵖᵈ : ∀ (D : PDataD) {ps} → Carrierᵖᵈ D ps ℓ → Set _
Coalgᵖᵈ D X = ∀ {is} → X is → ⟦ D ⟧ᵖᵈ X is

Coalgᵈ : ∀ (D : DataD) {ℓs ps} → Carrierᵈ D ℓs ps ℓ → Set _
Coalgᵈ D X = ∀ {is} → X is → ⟦ D ⟧ᵈ X is

IndCarrierʳ : {I : Set ℓⁱ} (D : RecD I rb) (X : I → Set ℓˣ) (ℓ : Level) → Set _
IndCarrierʳ D X ℓ = ∀ i → X i → Set ℓ

IndCarrierᶜ : {I : Set ℓⁱ} (D : ConD I cb) (X : Carrierᶜ D ℓˣ) (ℓ : Level) → Set _
IndCarrierᶜ D X ℓ = ∀ i → X i → Set ℓ

IndCarrierᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) (X : Carrierᶜˢ D ℓˣ) (ℓ : Level) → Set _
IndCarrierᶜˢ D X ℓ = ∀ i → X i → Set ℓ

IndCarrierᵖᵈ : ∀ (D : PDataD) {ps} (X : Carrierᵖᵈ D ps ℓˣ) (ℓ : Level) → Set _
IndCarrierᵖᵈ D {ps} X ℓ = IndCarrierᶜˢ (PDataD.applyP D ps) X ℓ

IndCarrierᵈ : ∀ (D : DataD) {ℓs ps} (X : Carrierᵈ D ℓs ps ℓˣ) ℓ → Set _
IndCarrierᵈ D {ℓs} = IndCarrierᵖᵈ (DataD.applyL D ℓs)

Allʳ : {I : Set ℓⁱ} (D : RecD I rb) {X : I → Set ℓˣ} (Y : IndCarrierʳ D X ℓʸ)
       (xs : ⟦ D ⟧ʳ X) → Set (max-ℓ rb ⊔ ℓʸ)
Allʳ (ι i  ) Y x  = Y i x
Allʳ (π A D) Y xs = (a : A) → Allʳ (D a) Y (xs a)

Allᶜ : {I : Set ℓⁱ} (D : ConD I cb) {X : Carrierᶜ D ℓˣ} (Y : IndCarrierᶜ D X ℓʸ)
       {i : I} (xs : ⟦ D ⟧ᶜ X i) (ℓ : Level) → Set (max-π cb ⊔ hasRec? ℓʸ cb ⊔ ℓ)
Allᶜ (ι i  ) Y _          ℓ = Lift ℓ ⊤
Allᶜ (ρ D E) Y (xs , xs') ℓ = Allʳ D Y xs × Allᶜ E Y xs' ℓ
Allᶜ (σ A D) Y (a  , xs ) ℓ = Allᶜ (D a) Y xs ℓ

Allᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) {X : Carrierᶜˢ D ℓˣ} (Y : IndCarrierᶜˢ D X ℓʸ)
        {i : I} (xs : ⟦ D ⟧ᶜˢ X i) (ℓ : Level)
      → Set (maxMap max-π cbs ⊔ maxMap (hasRec? ℓʸ) cbs ⊔ ℓ)
Allᶜˢ {cbs = _  ∷ cbs} {ℓʸ = ℓʸ} (D ∷ Ds) Y (inl xs) ℓ =
  Allᶜ  D  Y xs (ℓ ⊔ maxMap max-π cbs ⊔ maxMap (hasRec? ℓʸ) cbs)
Allᶜˢ {cbs = cb ∷ _  } {ℓʸ = ℓʸ} (D ∷ Ds) Y (inr xs) ℓ =
  Allᶜˢ Ds Y xs (ℓ ⊔ max-π cb ⊔ hasRec? ℓʸ cb)

Allᵖᵈ : ∀ (D : PDataD) {ps} {X : Carrierᵖᵈ D ps ℓˣ} (Y : IndCarrierᵖᵈ D X ℓʸ)
      → ∀ {is} (xs : ⟦ D ⟧ᵖᵈ X is) → Set _
Allᵖᵈ D {ps} Y xs = Allᶜˢ (PDataD.applyP D ps) Y xs lzero

Allᵈ : ∀ (D : DataD) {ℓs ps} {X : Carrierᵈ D ℓs ps ℓˣ} (Y : IndCarrierᵈ D X ℓʸ)
     → ∀ {is} (xs : ⟦ D ⟧ᵈ X is) → Set _
Allᵈ D {ℓs} Y xs = Allᵖᵈ (DataD.applyL D ℓs) Y xs

IndAlgᶜ : {I : Set ℓⁱ} (D : ConD I cb) {X : Carrierᶜ D ℓˣ}
        → Algᶜ D X → IndCarrierᶜ D X ℓʸ → Set _
IndAlgᶜ D f Y = ∀ {i} xs → Allᶜ D Y xs lzero → Y i (f xs)

IndAlgᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) {X : Carrierᶜˢ D ℓˣ}
         → Algᶜˢ D X → IndCarrierᶜˢ D X ℓʸ → Set _
IndAlgᶜˢ D f Y = ∀ {i} xs → Allᶜˢ D Y xs lzero → Y i (f xs)

IndAlgᵖᵈ : ∀ (D : PDataD) {ps} {X : Carrierᵖᵈ D ps ℓˣ}
         → Algᵖᵈ D X → IndCarrierᵖᵈ D X ℓʸ → Set _
IndAlgᵖᵈ D f Y = ∀ {is} xs → Allᵖᵈ D Y xs → Y is (f xs)

IndAlgᵈ : ∀ (D : DataD) {ℓs ps} {X : Carrierᵈ D ℓs ps ℓˣ}
        → Algᵈ D X → IndCarrierᵈ D X ℓ → Set _
IndAlgᵈ D f Y = ∀ {is} xs → Allᵈ D Y xs → Y is (f xs)

ind-fmapʳ : {I : Set ℓⁱ} (D : RecD I rb) {X : I → Set ℓˣ} {Y : IndCarrierʳ D X ℓʸ}
          → (∀ {i} x → Y i x) → (xs : ⟦ D ⟧ʳ X) → Allʳ D Y xs
ind-fmapʳ (ι i  ) f x  = f x
ind-fmapʳ (π A D) f xs = λ a → ind-fmapʳ (D a) f (xs a)

ind-fmapᶜ : {I : Set ℓⁱ} (D : ConD I cb) {X : Carrierᶜ D ℓˣ} {Y : IndCarrierᶜ D X ℓʸ}
          → (∀ {i} x → Y i x) → ∀ {i} (xs : ⟦ D ⟧ᶜ X i) → Allᶜ D Y xs ℓ
ind-fmapᶜ (ι i  ) f _          = lift tt
ind-fmapᶜ (σ A D) f (a , xs)   = ind-fmapᶜ (D a) f xs
ind-fmapᶜ (ρ D E) f (xs , xs') = ind-fmapʳ D f xs , ind-fmapᶜ E f xs'

ind-fmapᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) {X : Carrierᶜˢ D ℓˣ} {Y : IndCarrierᶜˢ D X ℓʸ}
           → (∀ {i} x → Y i x) → ∀ {i} (xs : ⟦ D ⟧ᶜˢ X i) → Allᶜˢ D Y xs ℓ
ind-fmapᶜˢ (D ∷ Ds) f (inl xs) = ind-fmapᶜ  D  f xs
ind-fmapᶜˢ (D ∷ Ds) f (inr xs) = ind-fmapᶜˢ Ds f xs

ind-fmapᵖᵈ : ∀ (D : PDataD) {ps} {X : Carrierᵖᵈ D ps ℓˣ} {Y : IndCarrierᵖᵈ D X ℓʸ}
           → (∀ {is} x → Y is x) → ∀ {is} (xs : ⟦ D ⟧ᵖᵈ X is) → Allᵖᵈ D Y xs
ind-fmapᵖᵈ D {ps = ps} = ind-fmapᶜˢ (PDataD.applyP D ps)

ind-fmapᵈ : ∀ (D : DataD) {ℓs ps} {X : Carrierᵈ D ℓs ps ℓˣ} {Y : IndCarrierᵈ D X ℓʸ}
           → (∀ {is} x → Y is x) → ∀ {is} (xs : ⟦ D ⟧ᵈ X is) → Allᵈ D Y xs
ind-fmapᵈ D {ℓs} = ind-fmapᵖᵈ (DataD.applyL D ℓs)
