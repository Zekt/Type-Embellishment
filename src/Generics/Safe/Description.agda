{-# OPTIONS --safe --without-K #-}

module Generics.Safe.Description where

open import Prelude
open import Prelude.List as List
open import Prelude.Sum as Sum
open import Generics.Safe.Telescope

RecB : Set
RecB = List Level

ConB : Set
ConB = List (Level ⊎ RecB)

ConBs : Set
ConBs = List ConB

max-ℓ : List Level → Level
max-ℓ = foldr lzero _⊔_

maxMap : {A : Set} → (A → Level) → List A → Level
maxMap f = max-ℓ ∘ List.map f

ρ-level : Level ⊎ RecB → Level
ρ-level (inl _ ) = lzero
ρ-level (inr rb) = max-ℓ rb

has-ρ? : Level → Level ⊎ RecB → Level
has-ρ? ℓ (inl _) = lzero
has-ρ? ℓ (inr _) = ℓ

σ-level : Level ⊎ RecB → Level
σ-level (inl ℓ) = ℓ
σ-level (inr _) = lzero

max-π : ConB → Level
max-π = maxMap ρ-level

max-σ : ConB → Level
max-σ = maxMap σ-level

hasRec? : Level → ConB → Level
hasRec? ℓ = maxMap (has-ρ? ℓ)

hasCon? : Level → ConBs → Level
hasCon? ℓ = maxMap (λ _ → ℓ)

maxMap-bound : {A : Set} (f : A → Level) (ℓ : Level)
             → (∀ a → f a ⊑ ℓ) → ∀ as → maxMap f as ⊑ ℓ
maxMap-bound f ℓ eq []       = refl
maxMap-bound f ℓ eq (a ∷ as) = cong₂ _⊔_ (eq a) (maxMap-bound f ℓ eq as)

hasRec?-bound : ∀ ℓ cb → hasRec? ℓ cb ⊑ ℓ
hasRec?-bound ℓ []            = refl
hasRec?-bound ℓ (inl ℓ' ∷ cb) = hasRec?-bound ℓ cb
hasRec?-bound ℓ (inr rb ∷ cb) = hasRec?-bound ℓ cb

hasCon?-bound : ∀ ℓ cbs → hasCon? ℓ cbs ⊑ ℓ
hasCon?-bound ℓ = maxMap-bound (λ _ → ℓ) ℓ (λ _ → refl)

private variable
    rb  : RecB
    cb  : ConB
    cbs : ConBs

module _ (I : Set ℓⁱ) where

  data RecD : RecB → Setω where
    ι : (i : I) → RecD []
    π : (A : Set ℓ) (D : A → RecD rb) → RecD (ℓ ∷ rb)


  data ConD : ConB → Setω where
    ι : (i : I) → ConD []
    σ : (A : Set ℓ) (D : A → ConD cb) → ConD (inl ℓ  ∷ cb)
    ρ : (D : RecD rb) (E : ConD cb)   → ConD (inr rb ∷ cb)

  data ConDs : ConBs → Setω where
    []  : ConDs []
    _∷_ : (D : ConD cb) (Ds : ConDs cbs) → ConDs (cb ∷ cbs)

  syntax π A (λ x → R) = Π[ x ∶ A ] R
  syntax σ A (λ x → D) = Σ[ x ∶ A ] D

record PDataD : Setω where
  constructor pdatad
  field
    alevel   : Level
    {plevel} : Level
    {ilevel} : Level
    {struct} : ConBs
  dlevel : Level
  dlevel = alevel ⊔ ilevel
  flevel : Level → Level
  flevel ℓ = maxMap max-π struct ⊔ maxMap max-σ struct ⊔
             maxMap (hasRec? ℓ) struct ⊔ hasCon? ilevel struct
  field
    level-pre-fixed-point : flevel dlevel ⊑ dlevel
    Param  : Tel plevel
    Index  : ⟦ Param ⟧ᵗ → Tel ilevel
    applyP : (p : ⟦ Param ⟧ᵗ) → ConDs ⟦ Index p ⟧ᵗ struct

record DataD : Setω where
  constructor datad
  field
    #levels : ℕ
  Levels : Set
  Levels = Level ^ #levels
  field
    applyL : Levels → PDataD

module _ {I : Set ℓⁱ} where

  ⟦_⟧ʳ : RecD I rb → (I → Set ℓ) → Set (max-ℓ rb ⊔ ℓ)
  ⟦ ι i   ⟧ʳ X = X i
  ⟦ π A D ⟧ʳ X = (a : A) → ⟦ D a ⟧ʳ X

  ⟦_⟧ᶜ : ConD I cb → (I → Set ℓ) → (I → Set (max-π cb ⊔ max-σ cb ⊔ hasRec? ℓ cb ⊔ ℓⁱ))
  ⟦ ι i   ⟧ᶜ X j = i ≡ j
  ⟦ σ A D ⟧ᶜ X j = Σ A λ a → ⟦ D a ⟧ᶜ X j
  ⟦ ρ D E ⟧ᶜ X j = Σ (⟦ D ⟧ʳ X) λ _ → ⟦ E ⟧ᶜ X j

  ⟦_⟧ᶜˢ : ConDs I cbs → (I → Set ℓ) → (I → Set (maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔
                                                maxMap (hasRec? ℓ) cbs ⊔ hasCon? ℓⁱ cbs))
  ⟦ []     ⟧ᶜˢ X i = ⊥
  ⟦ D ∷ Ds ⟧ᶜˢ X i = ⟦ D ⟧ᶜ X i ⊎ ⟦ Ds ⟧ᶜˢ X i

⟦_⟧ᵖᵈ : (D : PDataD) {p : ⟦ PDataD.Param D ⟧ᵗ}
      → let I = ⟦ PDataD.Index D p ⟧ᵗ in (I → Set ℓ) → (I → Set (PDataD.flevel D ℓ))
⟦ D ⟧ᵖᵈ {p} = ⟦ PDataD.applyP D p ⟧ᶜˢ

⟦_⟧ᵈ : (D : DataD) {ℓs : DataD.Levels D} → let Dᵖ = DataD.applyL D ℓs in
       {p : ⟦ PDataD.Param Dᵖ ⟧ᵗ}
     → let I = ⟦ PDataD.Index Dᵖ p ⟧ᵗ in (I → Set ℓ) → (I → Set (PDataD.flevel Dᵖ ℓ))
⟦ D ⟧ᵈ {ℓs} = ⟦ DataD.applyL D ℓs ⟧ᵖᵈ

fmapʳ : {I : Set ℓⁱ} (D : RecD I rb) {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
      → ({i : I} → X i → Y i) → ⟦ D ⟧ʳ X → ⟦ D ⟧ʳ Y
fmapʳ (ι i  ) f x  = f x
fmapʳ (π A D) f xs = λ a → fmapʳ (D a) f (xs a)

fmapᶜ : {I : Set ℓⁱ} (D : ConD I cb) {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
      → ({i : I} → X i → Y i) → {i : I} → ⟦ D ⟧ᶜ X i → ⟦ D ⟧ᶜ Y i
fmapᶜ (ι i  ) f eq       = eq
fmapᶜ (σ A D) f (a , xs) = a , fmapᶜ (D a) f xs
fmapᶜ (ρ D E) f (x , xs) = fmapʳ D f x , fmapᶜ E f xs

fmapᶜˢ : {I : Set ℓ} (Ds : ConDs I cbs) {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
       → ({i : I} → X i → Y i) → {i : I} → ⟦ Ds ⟧ᶜˢ X i → ⟦ Ds ⟧ᶜˢ Y i
fmapᶜˢ (D ∷ Ds) f (inl xs) = inl (fmapᶜ  D  f xs)
fmapᶜˢ (D ∷ Ds) f (inr xs) = inr (fmapᶜˢ Ds f xs)

fmapᵖᵈ : (D : PDataD) {p : ⟦ PDataD.Param D ⟧ᵗ} → let I = ⟦ PDataD.Index D p ⟧ᵗ in
         {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
       → ({i : I} → X i → Y i) → {i : I} → ⟦ D ⟧ᵖᵈ X i → ⟦ D ⟧ᵖᵈ Y i
fmapᵖᵈ D {p} = fmapᶜˢ (PDataD.applyP D p)

fmapᵈ : (D : DataD) {ℓs : DataD.Levels D} → let Dᵖ = DataD.applyL D ℓs in
        {p : ⟦ PDataD.Param Dᵖ ⟧ᵗ} → let I = ⟦ PDataD.Index Dᵖ p ⟧ᵗ in
        {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
      → ({i : I} → X i → Y i) → {i : I} → ⟦ D ⟧ᵈ X i → ⟦ D ⟧ᵈ Y i
fmapᵈ D {ℓs} = fmapᵖᵈ (DataD.applyL D ℓs)

ExtEqʳ : {I : Set ℓⁱ} (D : RecD I rb) {X : I → Set ℓˣ}
         (xs xs' : ⟦ D ⟧ʳ X) → Set (max-ℓ rb ⊔ ℓˣ)
ExtEqʳ (ι i  ) x  x'  = x ≡ x'
ExtEqʳ (π A D) xs xs' = (a : A) → ExtEqʳ (D a) (xs a) (xs' a)

Finitaryʳ : RecB → Set
Finitaryʳ = _≡ []

Finitaryᶜ : ConB → Set
Finitaryᶜ = All Sum.[ const ⊤ , Finitaryʳ ]

Finitaryᶜˢ : ConBs → Set
Finitaryᶜˢ = All Finitaryᶜ

Finitaryᵖᵈ : PDataD → Set
Finitaryᵖᵈ D = Finitaryᶜˢ (PDataD.struct D)

Finitary : DataD → Set
Finitary D = ∀ ℓs → Finitaryᵖᵈ (DataD.applyL D ℓs)
