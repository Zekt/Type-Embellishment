{-# OPTIONS --safe #-}

module Generics.Safe.RecursionScheme where

open import Prelude
open import Generics.Safe.Telescope; open ∀ℓω; open ∀ᵗ; open ∀ᵇᵗ
open import Generics.Safe.Description
open import Generics.Safe.Algebra
open import Generics.Safe.Recursion

private variable
  rb  : RecB
  cb  : ConB
  cbs : ConBs

FoldAlgTᶜ : {I : Set ℓⁱ} (D : ConD I cb) → (I → Set ℓ) → Set (max-π cb ⊔ max-σ cb ⊔ ℓ)
FoldAlgTᶜ (ι i  ) X = X i
FoldAlgTᶜ (σ A D) X = (a : A) → FoldAlgTᶜ (D a) X
FoldAlgTᶜ (ρ D E) X = ⟦ D ⟧ʳ X → FoldAlgTᶜ E X

FoldAlgTᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) → (I → Set ℓ)
           → Tel (maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ hasCon? ℓ cbs)
FoldAlgTᶜˢ []       X = []
FoldAlgTᶜˢ (D ∷ Ds) X = FoldAlgTᶜ D X ∷ constω (FoldAlgTᶜˢ Ds X)

FoldAlgTᵖᵈ : ∀ (D : PDataD) ps ℓ → Set _
FoldAlgTᵖᵈ D ps ℓ = {X : ∀ᵇᵗ false (PDataD.Index D ps) λ _ → Set ℓ}
                  → ∀ᵗ true (FoldAlgTᶜˢ (PDataD.applyP D ps) (X $$_)) λ _
                  → Algebraᵖᵈ D ps ℓ

FoldAlgTᵈ : ∀ (D : DataD) ℓs ps ℓ → Set _
FoldAlgTᵈ D ℓs = FoldAlgTᵖᵈ (DataD.applyL D ℓs)

fold-algᶜ : {I : Set ℓⁱ} (D : ConD I cb) {X : Carrierᶜ D ℓ} → FoldAlgTᶜ D X → Algᶜ D X
fold-algᶜ (ι i  ) f eq         = subst _ eq f
fold-algᶜ (σ A D) f (a  , xs ) = fold-algᶜ (D a) (f a ) xs
fold-algᶜ (ρ D E) f (xs , xs') = fold-algᶜ  E    (f xs) xs'

fold-algᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) {X : Carrierᶜˢ D ℓ}
           → ⟦ FoldAlgTᶜˢ D X ⟧ᵗ → Algᶜˢ D X
fold-algᶜˢ []       _        ()
fold-algᶜˢ (D ∷ Ds) (f , fs) (inl xs) = fold-algᶜ  D  f  xs
fold-algᶜˢ (D ∷ Ds) (f , fs) (inr xs) = fold-algᶜˢ Ds fs xs

fold-algᵖᵈ : (D : PDataD) → ∀ {ℓ} → ∀ᵇᵗ false _ λ ps → FoldAlgTᵖᵈ D ps ℓ
fold-algᵖᵈ D $$ ps $$ fs = algebra _ (fold-algᶜˢ (PDataD.applyP D ps) fs)

fold-algᵈ : (D : DataD) → ∀ℓω _ λ ℓs → ∀ {ℓ} → ∀ᵇᵗ false _ λ ps → FoldAlgTᵈ D ℓs ps ℓ
fold-algᵈ D $$ ℓs = fold-algᵖᵈ (DataD.applyL D ℓs)
