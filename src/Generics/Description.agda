module Generics.Description where

open import Prelude renaming (⊤ to Unit; ⊥ to Empty; ℕ to Nat; _⊎_ to Sum)

private
  variable
    ℓ ℓ' ℓᵃ ℓⁱ ℓʳ ℓˣ ℓʸ : Level
    ℓf ℓg : Level → Level

mutual

  {-# NO_UNIVERSE_CHECK #-}
  data Tel : Level → Set where
    ∅   : Tel lzero
    _▷_ : (T : Tel ℓ) (A : ⟦ T ⟧ᵗ → Set ℓ') → Tel (ℓ ⊔ ℓ')

  ⟦_⟧ᵗ : Tel ℓ → Set ℓ
  ⟦ ∅     ⟧ᵗ = Unit
  ⟦ T ▷ A ⟧ᵗ = Σ ⟦ T ⟧ᵗ A

infixl 4 _▷_

module _ (I : Set ℓⁱ) where

  {-# NO_UNIVERSE_CHECK #-}
  data RecD : Level → Set where
    ι : (i : I) → RecD lzero
    π : (A : Set ℓ) (D : A → RecD ℓ') → RecD (ℓ ⊔ ℓ')

  {-# NO_UNIVERSE_CHECK #-}
  data ConD : (Level → Level) → Set where
    ι : (i : I) → ConD (λ _ → lzero)
    ρ : (D : RecD ℓʳ) (E : ConD ℓf) → ConD (λ ℓ → ℓ ⊔ ℓʳ ⊔ ℓf ℓ)
    σ : (A : Set ℓᵃ) (D : A → ConD ℓf) → ConD (λ ℓ → ℓᵃ ⊔ ℓf ℓ)

  {-# NO_UNIVERSE_CHECK #-}
  data ConDs : (Level → Level) → Set where
    ∅   : ConDs (λ _ → lzero)
    _◁_ : (D : ConD ℓf) (Ds : ConDs ℓg) → ConDs (λ ℓ → ℓⁱ ⊔ ℓf ℓ ⊔ ℓg ℓ)

  infixr 4 _◁_

{-# NO_UNIVERSE_CHECK #-}
record DataD : Set where
  field
    {plevel} : Level
    {ilevel} : Level
    {flevel} : Level → Level
    level : Level
    level-pre-fixed-point : flevel level ⊔ level ≡ level
    Param : Tel plevel
    Index : ⟦ Param ⟧ᵗ → Tel ilevel
    Desc  : (p : ⟦ Param ⟧ᵗ) → ConDs ⟦ Index p ⟧ᵗ flevel

{-# NO_UNIVERSE_CHECK #-}
record UPDataD : Set where
  field
    #levels : Nat
  Levels : Set
  Levels = Level ^ #levels
  field
    Desc : Levels → DataD

module _ {I : Set ℓⁱ} where

  ⟦_⟧ʳ : RecD I ℓʳ → (I → Set ℓ) → Set (ℓʳ ⊔ ℓ)
  ⟦ ι i   ⟧ʳ X = X i
  ⟦ π A D ⟧ʳ X = (a : A) → ⟦ D a ⟧ʳ X

  ⟦_⟧ᶜ : ConD I ℓf → (I → Set ℓ) → (I → Set (ℓⁱ ⊔ ℓf ℓ))
  ⟦ ι i   ⟧ᶜ X j = i ≡ j
  ⟦ ρ D E ⟧ᶜ X j = Σ (⟦ D ⟧ʳ X) λ _ → ⟦ E ⟧ᶜ X j
  ⟦ σ A D ⟧ᶜ X j = Σ A λ a → ⟦ D a ⟧ᶜ X j

  ⟦_⟧ᶜˢ : ConDs I ℓf → (I → Set ℓ) → (I → Set (ℓf ℓ))
  ⟦ ∅      ⟧ᶜˢ X i = Empty
  ⟦ D ◁ Ds ⟧ᶜˢ X i = Sum (⟦ D ⟧ᶜ X i) (⟦ Ds ⟧ᶜˢ X i)

⟦_⟧ᵈ : (D : DataD) (p : ⟦ DataD.Param D ⟧ᵗ)
     → let I = ⟦ DataD.Index D p ⟧ᵗ in (I → Set ℓ) → (I → Set (DataD.flevel D ℓ))
⟦ D ⟧ᵈ p = ⟦ DataD.Desc D p ⟧ᶜˢ

⟦_⟧ᵘᵖᵈ : (D : UPDataD) (ℓs : UPDataD.Levels D) → let Dᵐ = UPDataD.Desc D ℓs in
         (p : ⟦ DataD.Param Dᵐ ⟧ᵗ)
       → let I = ⟦ DataD.Index Dᵐ p ⟧ᵗ in (I → Set ℓ) → (I → Set (DataD.flevel Dᵐ ℓ))
⟦ D ⟧ᵘᵖᵈ ℓs = ⟦ UPDataD.Desc D ℓs ⟧ᵈ

fmapʳ : {I : Set ℓⁱ} (D : RecD I ℓʳ) {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
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
