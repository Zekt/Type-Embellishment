{-# OPTIONS --safe #-}

module Generics.Description where

open import Generics.Prelude

-- data Tel ℓ : Set (lsuc ℓ) where
--   nil  : Tel ℓ
--   cons : (A : Set ℓ) (T : A → Tel ℓ) → Tel ℓ

-- ⟦_⟧ᵗ : ∀ {ℓ} → Tel ℓ → Set ℓ
-- ⟦ nil      ⟧ᵗ = Unit
-- ⟦ cons A T ⟧ᵗ = Σ A λ a → ⟦ T a ⟧ᵗ

mutual

  data Tel ℓ : Set (lsuc ℓ) where
    ∅   : Tel ℓ
    _▷_ : (T : Tel ℓ) (A : ⟦ T ⟧ᵗ → Set ℓ) → Tel ℓ

  ⟦_⟧ᵗ : ∀ {ℓ} → Tel ℓ → Set ℓ
  ⟦ ∅     ⟧ᵗ = Unit
  ⟦ T ▷ A ⟧ᵗ = Σ ⟦ T ⟧ᵗ A

infixl 4 _▷_

data RecD {ℓ} (I : Set ℓ) : Set (lsuc ℓ) where
  ι : (i : I) → RecD I
  π : (A : Set ℓ) (D : A → RecD I) → RecD I

⟦_⟧ʳ : ∀ {ℓ} {I : Set ℓ} → RecD I → (I → Set ℓ) → Set ℓ
⟦ ι i   ⟧ʳ X = X i
⟦ π A D ⟧ʳ X = (a : A) → ⟦ D a ⟧ʳ X

data ConD {ℓ} (I : Set ℓ) : Set (lsuc ℓ) where
  ι : (i : I) → ConD I
  ρ : (D : RecD I) (E : ConD I) → ConD I
  σ : (A : Set ℓ) (D : A → ConD I) → ConD I

⟦_⟧ᶜ : ∀ {ℓ} {I : Set ℓ} → ConD I → (I → Set ℓ) → (I → Set ℓ)
⟦ ι i   ⟧ᶜ X j = i ≡ j
⟦ ρ D E ⟧ᶜ X j = Σ (⟦ D ⟧ʳ X) λ _ → ⟦ E ⟧ᶜ X j
⟦ σ A D ⟧ᶜ X j = Σ A λ a → ⟦ D a ⟧ᶜ X j

data ConDs {ℓ} (I : Set ℓ) : Set (lsuc ℓ) where
  ∅   : ConDs I
  _◁_ : (D : ConD I) (Ds : ConDs I) → ConDs I

infixr 4 _◁_

⟦_⟧ᶜˢ : ∀ {ℓ} {I : Set ℓ} → ConDs I → (I → Set ℓ) → (I → Set ℓ)
⟦ ∅      ⟧ᶜˢ X i = Empty
⟦ D ◁ Ds ⟧ᶜˢ X i = Sum (⟦ D ⟧ᶜ X i) (⟦ Ds ⟧ᶜˢ X i)

record SetD {ℓᵖ ℓⁱ} : Set (lsuc (ℓᵖ ⊔ ℓⁱ)) where
  field
    Param : Tel ℓᵖ
    Index : ⟦ Param ⟧ᵗ → Tel ℓⁱ
    Desc  : (p : ⟦ Param ⟧ᵗ) → ConDs ⟦ Index p ⟧ᵗ

⟦_⟧ˢ : ∀ {ℓᵖ ℓⁱ} (D : SetD {ℓᵖ} {ℓⁱ}) {p : ⟦ SetD.Param D ⟧ᵗ}
     → let I = ⟦ SetD.Index D p ⟧ᵗ in (I → Set ℓⁱ) → (I → Set ℓⁱ)
⟦ D ⟧ˢ {p} = ⟦ SetD.Desc D p ⟧ᶜˢ

fmapʳ : ∀ {ℓ} {I : Set ℓ} (D : RecD I)
      → {X Y : I → Set ℓ} → ({i : I} → X i → Y i)
      → ⟦ D ⟧ʳ X → ⟦ D ⟧ʳ Y
fmapʳ (ι i  ) f x  = f x
fmapʳ (π A D) f xs = λ a → fmapʳ (D a) f (xs a)

fmapᶜ : ∀ {ℓ} {I : Set ℓ} (D : ConD I)
      → {X Y : I → Set ℓ} → ({i : I} → X i → Y i)
      → {i : I} → ⟦ D ⟧ᶜ X i → ⟦ D ⟧ᶜ Y i
fmapᶜ (ι i  ) f eq       = eq
fmapᶜ (ρ D E) f (x , xs) = fmapʳ D f x , fmapᶜ E f xs
fmapᶜ (σ A D) f (a , xs) = a , fmapᶜ (D a) f xs

fmapᶜˢ : ∀ {ℓ} {I : Set ℓ} (Ds : ConDs I)
       → {X Y : I → Set ℓ} → ({i : I} → X i → Y i)
       → {i : I} → ⟦ Ds ⟧ᶜˢ X i → ⟦ Ds ⟧ᶜˢ Y i
fmapᶜˢ (D ◁ Ds) f (inl xs) = inl (fmapᶜ  D  f xs)
fmapᶜˢ (D ◁ Ds) f (inr xs) = inr (fmapᶜˢ Ds f xs)

fmapˢ : ∀ {ℓᵖ ℓⁱ} (D : SetD {ℓᵖ} {ℓⁱ}) {p : ⟦ SetD.Param D ⟧ᵗ}
      → let I = ⟦ SetD.Index D p ⟧ᵗ
        in  {X Y : I → Set ℓⁱ} → ({i : I} → X i → Y i)
          → {i : I} → ⟦ D ⟧ˢ X i → ⟦ D ⟧ˢ Y i
fmapˢ D {p} = fmapᶜˢ (SetD.Desc D p)