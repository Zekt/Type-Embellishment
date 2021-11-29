{-# OPTIONS --safe #-}

module Generics.Description where

open import Generics.Prelude

private
  variable
    ℓ ℓ' ℓᵃ ℓⁱ ℓˣ ℓʸ : Level
    ℓf ℓg : Level → Level

mutual

  data Tel : Level → Setω where
    ∅   : Tel lzero
    _▷_ : (T : Tel ℓ) (A : ⟦ T ⟧ᵗ → Set ℓ') → Tel (ℓ ⊔ ℓ')

  ⟦_⟧ᵗ : Tel ℓ → Set ℓ
  ⟦ ∅     ⟧ᵗ = Unit
  ⟦ T ▷ A ⟧ᵗ = Σ ⟦ T ⟧ᵗ A

infixl 4 _▷_

data RecD (I : Set ℓⁱ) : (Level → Level) → Setω where
  ι : (i : I) → RecD I (λ ℓ → ℓ)
  π : (A : Set ℓᵃ) (D : A → RecD I ℓf) → RecD I (λ ℓ → ℓᵃ ⊔ ℓf ℓ)

⟦_⟧ʳ : {I : Set ℓⁱ} → RecD I ℓf → (I → Set ℓ) → Set (ℓf ℓ)
⟦ ι i   ⟧ʳ X = X i
⟦ π A D ⟧ʳ X = (a : A) → ⟦ D a ⟧ʳ X

data ConD (I : Set ℓⁱ) : (Level → Level) → Setω where
  ι : (i : I) → ConD I (λ _ → ℓⁱ)
  ρ : (D : RecD I ℓf) (E : ConD I ℓg) → ConD I (λ ℓ → ℓf ℓ ⊔ ℓg ℓ)
  σ : (A : Set ℓᵃ) (D : A → ConD I ℓf) → ConD I (λ ℓ → ℓᵃ ⊔ ℓf ℓ)

⟦_⟧ᶜ : {I : Set ℓⁱ} → ConD I ℓf → (I → Set ℓ) → (I → Set (ℓf ℓ))
⟦ ι i   ⟧ᶜ X j = i ≡ j
⟦ ρ D E ⟧ᶜ X j = Σ (⟦ D ⟧ʳ X) λ _ → ⟦ E ⟧ᶜ X j
⟦ σ A D ⟧ᶜ X j = Σ A λ a → ⟦ D a ⟧ᶜ X j

data ConDs (I : Set ℓⁱ) : (Level → Level) → Setω where
  ∅   : ConDs I (λ _ → lzero)
  _◁_ : (D : ConD I ℓf) (Ds : ConDs I ℓg) → ConDs I (λ ℓ → ℓf ℓ ⊔ ℓg ℓ)

infixr 4 _◁_

⟦_⟧ᶜˢ : {I : Set ℓⁱ} → ConDs I ℓf → (I → Set ℓ) → (I → Set (ℓf ℓ))
⟦ ∅      ⟧ᶜˢ X i = Empty
⟦ D ◁ Ds ⟧ᶜˢ X i = Sum (⟦ D ⟧ᶜ X i) (⟦ Ds ⟧ᶜˢ X i)

record DataD : Setω where
  field
    {plevel} : Level
    {ilevel} : Level
    {flevel} : Level → Level
    level : Level
    level-fixed-point : level ⊔ flevel level ≡ level
    Param : Tel plevel
    Index : ⟦ Param ⟧ᵗ → Tel ilevel
    Desc  : (p : ⟦ Param ⟧ᵗ) → ConDs ⟦ Index p ⟧ᵗ flevel

⟦_⟧ᵈ : (D : DataD) (p : ⟦ DataD.Param D ⟧ᵗ)
     → let I = ⟦ DataD.Index D p ⟧ᵗ in (I → Set ℓ) → (I → Set (DataD.flevel D ℓ))
⟦ D ⟧ᵈ p = ⟦ DataD.Desc D p ⟧ᶜˢ

record UPDataD : Setω where
  field
    #levels : Nat
  Levels : Set
  Levels = Level ^ #levels
  field
    Desc : Levels → DataD

⟦_⟧ᵘᵖᵈ : (D : UPDataD) (ℓs : UPDataD.Levels D) → let Dᵐ = UPDataD.Desc D ℓs in
         (p : ⟦ DataD.Param Dᵐ ⟧ᵗ)
       → let I = ⟦ DataD.Index Dᵐ p ⟧ᵗ in (I → Set ℓ) → (I → Set (DataD.flevel Dᵐ ℓ))
⟦ D ⟧ᵘᵖᵈ ℓs = ⟦ UPDataD.Desc D ℓs ⟧ᵈ

fmapʳ : {I : Set ℓⁱ} (D : RecD I ℓf) {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
      → ({i : I} → X i → Y i) → ⟦ D ⟧ʳ X → ⟦ D ⟧ʳ Y
fmapʳ (ι i  ) f x  = f x
fmapʳ (π A D) f xs = λ a → fmapʳ (D a) f (xs a)

fmapᶜ : {I : Set ℓⁱ} (D : ConD I ℓf) {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
      → ({i : I} → X i → Y i) → {i : I} → ⟦ D ⟧ᶜ X i → ⟦ D ⟧ᶜ Y i
fmapᶜ (ι i  ) f eq       = eq
fmapᶜ (ρ D E) f (x , xs) = fmapʳ D f x , fmapᶜ E f xs
fmapᶜ (σ A D) f (a , xs) = a , fmapᶜ (D a) f xs

fmapᶜˢ : {I : Set ℓ} (Ds : ConDs I ℓf) {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
       → ({i : I} → X i → Y i) → {i : I} → ⟦ Ds ⟧ᶜˢ X i → ⟦ Ds ⟧ᶜˢ Y i
fmapᶜˢ (D ◁ Ds) f (inl xs) = inl (fmapᶜ  D  f xs)
fmapᶜˢ (D ◁ Ds) f (inr xs) = inr (fmapᶜˢ Ds f xs)

fmapᵈ : (D : DataD) (p : ⟦ DataD.Param D ⟧ᵗ) → let I = ⟦ DataD.Index D p ⟧ᵗ in
        {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
      → ({i : I} → X i → Y i) → {i : I} → ⟦ D ⟧ᵈ p X i → ⟦ D ⟧ᵈ p Y i
fmapᵈ D p = fmapᶜˢ (DataD.Desc D p)

fmapᵘᵖᵈ : (D : UPDataD) (ℓs : UPDataD.Levels D) → let Dᵐ = UPDataD.Desc D ℓs in
          (p : ⟦ DataD.Param Dᵐ ⟧ᵗ) → let I = ⟦ DataD.Index Dᵐ p ⟧ᵗ in
          {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
        → ({i : I} → X i → Y i) → {i : I} → ⟦ D ⟧ᵘᵖᵈ ℓs p X i → ⟦ D ⟧ᵘᵖᵈ ℓs p Y i
fmapᵘᵖᵈ D ℓs = fmapᵈ (UPDataD.Desc D ℓs)