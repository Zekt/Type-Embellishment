{-# OPTIONS --safe --without-K #-}

module Generics.Safe.Algebra where

open import Prelude
open import Generics.Safe.Description

private
  variable
    rb  : RecB
    cb  : ConB
    cbs : ConBs

Carrierᶜ : {I : Set ℓⁱ} → ConD I cb → (ℓ : Level) → Set (ℓⁱ ⊔ lsuc ℓ)
Carrierᶜ {I = I} _ ℓ = I → Set ℓ

Algᶜ : {I : Set ℓⁱ} (D : ConD I cb) → Carrierᶜ D ℓ
     → Set (ℓ ⊔ ℓⁱ ⊔ max-π cb ⊔ max-σ cb ⊔ hasRec? ℓ cb)
Algᶜ D X = ∀ {i} → ⟦ D ⟧ᶜ X i → X i

Carrierᶜˢ : {I : Set ℓⁱ} → ConDs I cbs → (ℓ : Level) → Set (ℓⁱ ⊔ lsuc ℓ)
Carrierᶜˢ {I = I} _ ℓ = I → Set ℓ

Algᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) → Carrierᶜˢ D ℓ
      → Set (ℓ ⊔ ℓⁱ ⊔ maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔
             hasCon? ℓⁱ cbs ⊔ maxMap (hasRec? ℓ) cbs)
Algᶜˢ D X = ∀ {i} → ⟦ D ⟧ᶜˢ X i → X i

Carrierᵖᵈ : (D : PDataD) (ℓ : Level) → Set (PDataD.plevel D ⊔ PDataD.ilevel D ⊔ lsuc ℓ)
Carrierᵖᵈ D ℓ = (p : ⟦ PDataD.Param D ⟧ᵗ) → Carrierᶜˢ (PDataD.applyP D p) ℓ

Algᵖᵈ : (D : PDataD) → Carrierᵖᵈ D ℓ
      → Set (ℓ ⊔ PDataD.plevel D ⊔ PDataD.ilevel D ⊔ PDataD.flevel D ℓ)
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

Allʳ : {I : Set ℓⁱ} (D : RecD I rb) {X : I → Set ℓˣ} (Y : (i : I) → X i → Set ℓʸ)
       (xs : ⟦ D ⟧ʳ X) → Set (max-ℓ rb ⊔ ℓʸ)
Allʳ (ι i  ) Y x  = Y i x
Allʳ (π A D) Y xs = (a : A) → Allʳ (D a) Y (xs a)

PCarrierᶜ : {I : Set ℓⁱ} (D : ConD I cb) (X : Carrierᶜ D ℓˣ) (ℓ : Level)
          → Set (ℓⁱ ⊔ ℓˣ ⊔ lsuc ℓ)
PCarrierᶜ D X ℓ = ∀ i → X i → Set ℓ

Allᶜ : {I : Set ℓⁱ} (D : ConD I cb) {X : Carrierᶜ D ℓˣ} (Y : PCarrierᶜ D X ℓʸ)
       {i : I} (xs : ⟦ D ⟧ᶜ X i) (ℓ : Level) → Set (max-π cb ⊔ hasRec? ℓʸ cb ⊔ ℓ)
Allᶜ (ι i  ) Y _          ℓ = Lift ℓ ⊤
Allᶜ (ρ D E) Y (xs , xs') ℓ = Allʳ D Y xs × Allᶜ E Y xs' ℓ
Allᶜ (σ A D) Y (a  , xs ) ℓ = Allᶜ (D a) Y xs ℓ

PAlgᶜ : {I : Set ℓⁱ} (D : ConD I cb) {X : Carrierᶜ D ℓˣ} → Algᶜ D X → PCarrierᶜ D X ℓʸ
      → Set (ℓⁱ ⊔ max-π cb ⊔ max-σ cb ⊔ hasRec? ℓˣ cb ⊔ hasRec? ℓʸ cb ⊔ ℓʸ)
PAlgᶜ D f Y = ∀ {i} xs → Allᶜ D Y xs lzero → Y i (f xs)

PCarrierᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) (X : Carrierᶜˢ D ℓˣ) (ℓ : Level)
           → Set (ℓⁱ ⊔ ℓˣ ⊔ lsuc ℓ)
PCarrierᶜˢ D X ℓ = ∀ i → X i → Set ℓ

Allᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) {X : Carrierᶜˢ D ℓˣ} (Y : PCarrierᶜˢ D X ℓʸ)
        {i : I} (xs : ⟦ D ⟧ᶜˢ X i) (ℓ : Level)
      → Set (maxMap max-π cbs ⊔ maxMap (hasRec? ℓʸ) cbs ⊔ ℓ)
Allᶜˢ {cbs = _  ∷ cbs} {ℓʸ = ℓʸ} (D ∷ Ds) Y (inl xs) ℓ =
  Allᶜ  D  Y xs (ℓ ⊔ maxMap max-π cbs ⊔ maxMap (hasRec? ℓʸ) cbs)
Allᶜˢ {cbs = cb ∷ _  } {ℓʸ = ℓʸ} (D ∷ Ds) Y (inr xs) ℓ =
  Allᶜˢ Ds Y xs (ℓ ⊔ max-π cb ⊔ hasRec? ℓʸ cb)

PAlgᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) {X : Carrierᶜˢ D ℓˣ}
       → Algᶜˢ D X → PCarrierᶜˢ D X ℓʸ
       → Set (ℓⁱ ⊔ maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ hasCon? ℓⁱ cbs ⊔
              maxMap (hasRec? ℓˣ) cbs ⊔ maxMap (hasRec? ℓʸ) cbs ⊔ ℓʸ)
PAlgᶜˢ D f Y = ∀ {i} xs → Allᶜˢ D Y xs lzero → Y i (f xs)

PCarrierᵖᵈ : (D : PDataD) (X : Carrierᵖᵈ D ℓˣ) (ℓ : Level)
           → Set (ℓˣ ⊔ PDataD.plevel D ⊔ PDataD.ilevel D ⊔ lsuc ℓ)
PCarrierᵖᵈ D X ℓ = (p : ⟦ PDataD.Param D ⟧ᵗ) → PCarrierᶜˢ (PDataD.applyP D p) (X p) ℓ

Allᵖᵈ : (D : PDataD) {X : Carrierᵖᵈ D ℓˣ} (Y : PCarrierᵖᵈ D X ℓʸ)
      → {p : ⟦ PDataD.Param D ⟧ᵗ} {i : ⟦ PDataD.Index D p ⟧ᵗ} (xs : ⟦ D ⟧ᵖᵈ p (X p) i)
      → Set (maxMap max-π (PDataD.struct D) ⊔ maxMap (hasRec? ℓʸ) (PDataD.struct D))
Allᵖᵈ D Y {p} xs = Allᶜˢ (PDataD.applyP D p) (Y p) xs lzero

PAlgᵖᵈ : (D : PDataD) {X : Carrierᵖᵈ D ℓˣ} → Algᵖᵈ D X → PCarrierᵖᵈ D X ℓʸ
       → Set (ℓʸ ⊔ PDataD.plevel D ⊔ PDataD.ilevel D ⊔
              maxMap max-π (PDataD.struct D) ⊔ maxMap max-σ (PDataD.struct D) ⊔
              maxMap (hasRec? ℓˣ) (PDataD.struct D) ⊔
              maxMap (hasRec? ℓʸ) (PDataD.struct D) ⊔
              hasCon? (PDataD.ilevel D) (PDataD.struct D))
PAlgᵖᵈ D f Y = ∀ {p i} xs → Allᵖᵈ D Y xs → Y p i (f xs)

PCarrierᵈ : (D : DataD) {ℓf : DataD.Levels D → Level} (X : Carrierᵈ D ℓf)
          → (DataD.Levels D → Level) → Setω
PCarrierᵈ D X ℓg = (ℓs : DataD.Levels D)
                 → PCarrierᵖᵈ (DataD.applyL D ℓs) (X ℓs) (ℓg ℓs)

Allᵈ : (D : DataD) {ℓf ℓg : DataD.Levels D → Level}
       {X : Carrierᵈ D ℓf} (Y : PCarrierᵈ D X ℓg)
     → {ℓs : DataD.Levels D} → let Dᵖ = DataD.applyL D ℓs in
       {p : ⟦ PDataD.Param Dᵖ ⟧ᵗ} {i : ⟦ PDataD.Index Dᵖ p ⟧ᵗ}
       (xs : ⟦ D ⟧ᵈ ℓs p (X ℓs p) i)
     → Set (maxMap max-π (PDataD.struct Dᵖ) ⊔
            maxMap (hasRec? (ℓg ℓs)) (PDataD.struct Dᵖ))
Allᵈ D Y {ℓs} xs = Allᵖᵈ (DataD.applyL D ℓs) (Y ℓs) xs

PAlgᵈ : (D : DataD) {ℓf ℓg : DataD.Levels D → Level} {X : Carrierᵈ D ℓf}
      → Algᵈ D X → PCarrierᵈ D X ℓg → Setω
PAlgᵈ D f Y = ∀ {ℓs p i} xs → Allᵈ D Y xs → Y ℓs p i (f xs)

record PAlg (D : DataD) : Setω where
  field
    alg      : Alg D
    {flevel} : DataD.Levels D → Level
    PCarrier : PCarrierᵈ D (Alg.Carrier alg) flevel
    apply    : PAlgᵈ D (Alg.apply alg) PCarrier
