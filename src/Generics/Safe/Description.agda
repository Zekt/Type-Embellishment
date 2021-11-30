{-# OPTIONS --safe #-}

module Generics.Safe.Description where

open import Prelude renaming (⊤ to Unit; ⊥ to Empty; ℕ to Nat; _⊎_ to Sum)

_⊔'_ : (Level → Level) → (Level → Level) → (Level → Level)
(ℓf ⊔' ℓg) ℓ = ℓf ℓ ⊔ ℓg ℓ

private
  variable
    ℓ ℓ' ℓᵃ ℓⁱ ℓʳ ℓˣ ℓʸ : Level
    ℓρ ℓρ' ℓ◁ : Level → Level

mutual

  data Tel : Level → Setω where
    ∅   : Tel lzero
    _▷_ : (T : Tel ℓ) (A : ⟦ T ⟧ᵗ → Set ℓ') → Tel (ℓ ⊔ ℓ')

  ⟦_⟧ᵗ : Tel ℓ → Set ℓ
  ⟦ ∅     ⟧ᵗ = Unit
  ⟦ T ▷ A ⟧ᵗ = Σ ⟦ T ⟧ᵗ A

infixl 4 _▷_

module _ (I : Set ℓⁱ) where

  data RecD : Level → Setω where
    ι : (i : I) → RecD lzero
    π : (A : Set ℓ) (D : A → RecD ℓ') → RecD (ℓ ⊔ ℓ')

  data ConD : Level → (Level → Level) → Setω where
    ι : (i : I) → ConD lzero (const lzero)
    ρ : (D : RecD ℓʳ) (E : ConD ℓ ℓρ) → ConD (ℓʳ ⊔ ℓ) (id ⊔' ℓρ)
    σ : (A : Set ℓᵃ) (D : A → ConD ℓ ℓρ) → ConD (ℓᵃ ⊔ ℓ) ℓρ

  data ConDs : Level → (Level → Level) → (Level → Level) → Setω where
    ∅   : ConDs lzero (const lzero) (const lzero)
    _◁_ : (D : ConD ℓ ℓρ) (Ds : ConDs ℓ' ℓρ' ℓ◁) → ConDs (ℓ ⊔ ℓ') (ℓρ ⊔' ℓρ') (id ⊔' ℓ◁)

  infixr 4 _◁_

record DataD : Setω where
  field
    {plevel} : Level
    {ilevel} : Level
    {alevel} : Level
    {rlevel} : Level → Level
    {clevel} : Level → Level
  flevel : Level → Level
  flevel ℓ = alevel ⊔ rlevel ℓ ⊔ clevel ilevel
  field
    level : Level
    level-pre-fixed-point : flevel level ⊔ level ≡ level
    Param : Tel plevel
    Index : ⟦ Param ⟧ᵗ → Tel ilevel
    Desc  : (p : ⟦ Param ⟧ᵗ) → ConDs ⟦ Index p ⟧ᵗ alevel rlevel clevel

record UPDataD : Setω where
  field
    #levels : Nat
  Levels : Set
  Levels = Level ^ #levels
  field
    Desc : Levels → DataD

module _ {I : Set ℓⁱ} where

  ⟦_⟧ʳ : RecD I ℓᵃ → (I → Set ℓ) → Set (ℓᵃ ⊔ ℓ)
  ⟦ ι i   ⟧ʳ X = X i
  ⟦ π A D ⟧ʳ X = (a : A) → ⟦ D a ⟧ʳ X

  ⟦_⟧ᶜ : ConD I ℓᵃ ℓρ → (I → Set ℓ) → (I → Set (ℓᵃ ⊔ ℓρ ℓ ⊔ ℓⁱ))
  ⟦ ι i   ⟧ᶜ X j = i ≡ j
  ⟦ ρ D E ⟧ᶜ X j = Σ (⟦ D ⟧ʳ X) λ _ → ⟦ E ⟧ᶜ X j
  ⟦ σ A D ⟧ᶜ X j = Σ A λ a → ⟦ D a ⟧ᶜ X j

  ⟦_⟧ᶜˢ : ConDs I ℓᵃ ℓρ ℓ◁ → (I → Set ℓ) → (I → Set (ℓᵃ ⊔ ℓρ ℓ ⊔ ℓ◁ ℓⁱ))
  ⟦ ∅      ⟧ᶜˢ X i = Empty
  ⟦ D ◁ Ds ⟧ᶜˢ X i = Sum (⟦ D ⟧ᶜ X i) (⟦ Ds ⟧ᶜˢ X i)

⟦_⟧ᵈ : (D : DataD) (p : ⟦ DataD.Param D ⟧ᵗ)
     → let I = ⟦ DataD.Index D p ⟧ᵗ in (I → Set ℓ) → (I → Set (DataD.flevel D ℓ))
⟦ D ⟧ᵈ p = ⟦ DataD.Desc D p ⟧ᶜˢ

⟦_⟧ᵘᵖᵈ : (D : UPDataD) (ℓs : UPDataD.Levels D) → let Dᵐ = UPDataD.Desc D ℓs in
         (p : ⟦ DataD.Param Dᵐ ⟧ᵗ)
       → let I = ⟦ DataD.Index Dᵐ p ⟧ᵗ in (I → Set ℓ) → (I → Set (DataD.flevel Dᵐ ℓ))
⟦ D ⟧ᵘᵖᵈ ℓs = ⟦ UPDataD.Desc D ℓs ⟧ᵈ

fmapʳ : {I : Set ℓⁱ} (D : RecD I ℓᵃ) {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
      → ({i : I} → X i → Y i) → ⟦ D ⟧ʳ X → ⟦ D ⟧ʳ Y
fmapʳ (ι i  ) f x  = f x
fmapʳ (π A D) f xs = λ a → fmapʳ (D a) f (xs a)

fmapᶜ : {I : Set ℓⁱ} (D : ConD I ℓᵃ ℓρ) {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
      → ({i : I} → X i → Y i) → {i : I} → ⟦ D ⟧ᶜ X i → ⟦ D ⟧ᶜ Y i
fmapᶜ (ι i  ) f eq       = eq
fmapᶜ (ρ D E) f (x , xs) = fmapʳ D f x , fmapᶜ E f xs
fmapᶜ (σ A D) f (a , xs) = a , fmapᶜ (D a) f xs

fmapᶜˢ : {I : Set ℓ} (Ds : ConDs I ℓᵃ ℓρ ℓ◁) {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
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
