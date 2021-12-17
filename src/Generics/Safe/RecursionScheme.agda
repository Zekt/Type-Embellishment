{-# OPTIONS --safe #-}

module Generics.Safe.RecursionScheme where

open import Prelude
open import Generics.Safe.Telescope
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

FoldAlgTᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) → (I → Set ℓ) → Set ℓ'
           → Set (maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ hasCon? ℓ cbs ⊔ ℓ')
FoldAlgTᶜˢ []       X T = T
FoldAlgTᶜˢ (D ∷ Ds) X T = FoldAlgTᶜ D X → FoldAlgTᶜˢ Ds X T

FoldAlgTᵖᵈ : ∀ (D : PDataD) ps ℓ → Set _
FoldAlgTᵖᵈ D ps ℓ = (X : Curriedᵗ (PDataD.Index D ps) λ _ → Set ℓ)
                  → FoldAlgTᶜˢ (PDataD.applyP D ps)
                               (uncurryᵗ (PDataD.Index D ps) (λ _ → Set ℓ) X)
                               (Algebraᵖᵈ D ps ℓ)

FoldAlgTᵈ : ∀ (D : DataD) ℓs ps ℓ → Set _
FoldAlgTᵈ D ℓs = FoldAlgTᵖᵈ (DataD.applyL D ℓs)

fold-algᶜ : {I : Set ℓⁱ} (D : ConD I cb) {X : Carrierᶜ D ℓ} → FoldAlgTᶜ D X → Algᶜ D X
fold-algᶜ (ι i  ) f eq         = subst _ eq f
fold-algᶜ (σ A D) f (a , xs)   = fold-algᶜ (D a) (f a ) xs
fold-algᶜ (ρ D E) f (xs , xs') = fold-algᶜ  E    (f xs) xs'

fold-algᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) {X : Carrierᶜˢ D ℓ} (T : Set ℓ')
           → (Algᶜˢ D X → T) → FoldAlgTᶜˢ D X T
fold-algᶜˢ []       T cont = cont λ ()
fold-algᶜˢ (D ∷ Ds) T cont = λ f → fold-algᶜˢ Ds T λ g →
                             cont λ { (inl xs) → fold-algᶜ D f xs; (inr xs) → g xs }

fold-algᵖᵈ : (D : PDataD) → ∀ ps ℓ → FoldAlgTᵖᵈ D ps ℓ
fold-algᵖᵈ D ps ℓ X = fold-algᶜˢ (PDataD.applyP D ps) (Algebraᵖᵈ D ps ℓ)
                                 (algebra (uncurryᵗ _ _ X))

fold-algᵈ : (D : DataD) → ∀ ℓs ps ℓ → FoldAlgTᵈ D ℓs ps ℓ
fold-algᵈ D ℓs = fold-algᵖᵈ (DataD.applyL D ℓs)
