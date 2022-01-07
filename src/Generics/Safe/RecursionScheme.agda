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

FoldAlgTᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) → (I → Set ℓ)
           → Tel (maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ hasCon? ℓ cbs)
FoldAlgTᶜˢ []       X = []
FoldAlgTᶜˢ (D ∷ Ds) X = FoldAlgTᶜ D X ∷ constω (FoldAlgTᶜˢ Ds X)

fold-algᶜ : {I : Set ℓⁱ} (D : ConD I cb) {X : Carrierᶜ D ℓ} → FoldAlgTᶜ D X → Algᶜ D X
fold-algᶜ (ι i  ) f refl       = f
fold-algᶜ (σ A D) f (a  , xs ) = fold-algᶜ (D a) (f a ) xs
fold-algᶜ (ρ D E) f (xs , xs') = fold-algᶜ  E    (f xs) xs'

fold-algᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) {X : Carrierᶜˢ D ℓ}
           → ⟦ FoldAlgTᶜˢ D X ⟧ᵗ → Algᶜˢ D X
fold-algᶜˢ []       _        ()
fold-algᶜˢ (D ∷ Ds) (f , fs) (inl xs) = fold-algᶜ  D  f  xs
fold-algᶜˢ (D ∷ Ds) (f , fs) (inr xs) = fold-algᶜˢ Ds fs xs

fold-alg : ∀ {D N} → DataC D N → FoldP
fold-alg {D} C = record
  { Conv    = C
  ; #levels = suc (DataD.#levels D)
  ; levels  = snd
  ; Param   = λ (ℓ , ℓs) → let Dᵖ = DataD.applyL D ℓs in
      PDataD.Param Dᵖ
      ++ λ ps → (Curriedᵗ (PDataD.Index Dᵖ ps) (λ _ → Set ℓ) ∷ constω [])
      ++ λ (X , _) → FoldAlgTᶜˢ (PDataD.applyP Dᵖ ps) (λ is → uncurryᵗ _ _ X is)
  ; param   = λ _ (ps , _) → ps
  ; Carrier = λ _ (ps , (X , _) , args) → uncurryᵗ _ _ X
  ; apply   = λ { (ℓ , ℓs) (ps , (X , _) , args) →
                fold-algᶜˢ (PDataD.applyP (DataD.applyL D ℓs) ps) {!!} } }

{-
Failed to solve the following constraints:
  foldr lzero _⊔_ (map (λ _ → ℓ) (PDataD.struct (DataD.applyL D ℓs)))
  ⊔
  foldr lzero _⊔_
  (map (λ x → foldr lzero _⊔_ (map ρ-level x))
   (PDataD.struct (DataD.applyL D ℓs)))
  ⊔
  foldr lzero _⊔_
  (map (λ x → foldr lzero _⊔_ (map σ-level x))
   (PDataD.struct (DataD.applyL D ℓs)))
    = foldr lzero _⊔_ (map max-π (PDataD.struct (DataD.applyL D ℓs))) ⊔
      foldr lzero _⊔_ (map max-σ (PDataD.struct (DataD.applyL D ℓs)))
      ⊔
      foldr lzero _⊔_ (map (λ _ → ℓ) (PDataD.struct (DataD.applyL D ℓs)))
    (blocked on _ℓ_165)
-}

