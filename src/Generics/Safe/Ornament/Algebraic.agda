{-# OPTIONS --safe #-}

module Generics.Safe.Ornament.Algebraic where

open import Prelude renaming (⊤ to Unit; ⊥ to Empty; _⊎_ to Sum)
open import Generics.Safe.Description
open import Generics.Safe.Ornament.Description

private
  variable
    ℓ ℓ' ℓᵃ ℓⁱ ℓʳ : Level
    cρ : ℕ
    cρs : List ℕ

algODʳ : {I : Set ℓⁱ} (D : RecD I ℓʳ)
         {X : I → Set ℓ} (xs : ⟦ D ⟧ʳ X) → RecOD (Σ I X) fst D
algODʳ (ι i  ) x  = ι (_ , x) refl
algODʳ (π A D) xs = π λ a → algODʳ (D a) (xs a)

algODᶜ : {I : Set ℓⁱ} (D : ConD I ℓᵃ cρ)
         {X : I → Set ℓ} → (∀ {i} → ⟦ D ⟧ᶜ X i → X i)
        → ConOD (Σ I X) fst D (ℓᵃ ⊔ lcond cρ ℓ)
algODᶜ (ι i  )     alg = ι (_ , alg refl) refl
algODᶜ (ρ D E) {X} alg = Δ (⟦ D ⟧ʳ X) λ xs →
                         ρ (algODʳ D xs) (algODᶜ E (λ xs' → alg (xs , xs')))
algODᶜ (σ A D)     alg = σ λ a → algODᶜ (D a) λ xs → alg (a , xs)

algODᶜˢ : {I : Set ℓⁱ} (D : ConDs I ℓᵃ cρs)
          {X : I → Set ℓ} → (∀ {i} → ⟦ D ⟧ᶜˢ X i → X i)
        → ConODs (Σ I X) fst D (ℓᵃ ⊔ lconds cρs ℓ) cρs
algODᶜˢ ∅        alg = ∅
algODᶜˢ (D ◁ Ds) alg = algODᶜ  D  (λ xs → alg (inl xs))
                   ◁ ◂ algODᶜˢ Ds (λ xs → alg (inr xs))

algODᵈ : (D : DataD)
       → (X : (p : ⟦ DataD.Param D ⟧ᵗ) (i : ⟦ DataD.Index D p ⟧ᵗ) → Set ℓ)
       → (∀ {p i} → ⟦ D ⟧ᵈ p (X p) i → X p i)
       → DataOD D
algODᵈ {ℓ} D X alg = record
  { level = DataD.level D ⊔ lcond (length (DataD.recCounts D)) ℓ
                          ⊔ lconds        (DataD.recCounts D)  ℓ
  ; level-pre-fixed-point = pfp (DataD.recCounts D)
                                (DataD.alevel D) (DataD.ilevel D) (DataD.level D)
                                (DataD.level-pre-fixed-point D)
  ; Param = DataD.Param D
  ; param = id
  ; Index = λ p → DataD.Index D p ▷ X p
  ; index = λ _ → fst
  ; OrnDesc = λ p → algODᶜˢ (DataD.Desc D p) alg
  }
  where
  pfp : (ns : List ℕ) (ℓᵃ ℓⁱ ℓ' : Level)
      → ℓᵃ ⊔ ℓ' ⊔ lcond (length ns) ℓⁱ ⊔ lconds ns ℓ' ≡ ℓ'
      → ℓᵃ ⊔ ℓ' ⊔ lcond (length ns) ℓ ⊔ lcond (length ns) (ℓⁱ ⊔ ℓ)
        ⊔ lconds ns ℓ ⊔ lconds ns (ℓ' ⊔ lcond (length ns) ℓ ⊔ lconds ns ℓ)
      ≡ ℓ' ⊔ lcond (length ns) ℓ ⊔ lconds ns ℓ
  pfp ns ℓᵃ ℓⁱ ℓ' eq =
    trans (cong (ℓᵃ ⊔_)
             (cong₂ _⊔_ (sym (lconds-upper-bound ns ℓ'))
             (cong₂ _⊔_ (lcond-preserves-⊔ (length ns) ℓ ℓⁱ)
                        (lconds-upper-bound ns
                           (ℓ' ⊔ lcond (length ns) ℓ ⊔ lconds ns ℓ)))))
          (cong ((lcond (length ns) ℓ ⊔ lconds ns ℓ) ⊔_) eq)

algODᵘᵖᵈ : (D : UPDataD)
         → (X : (ℓs : UPDataD.Levels D)
                (p  : ⟦ DataD.Param (UPDataD.Desc D ℓs) ⟧ᵗ)
                (i  : ⟦ DataD.Index (UPDataD.Desc D ℓs) p ⟧ᵗ) → Set ℓ)
         → (∀ {ℓs p i} → ⟦ D ⟧ᵘᵖᵈ ℓs p (X ℓs p) i → X ℓs p i)
         → UPDataOD D
algODᵘᵖᵈ D X alg = record
  { #levels = UPDataD.#levels D
  ; levels  = id
  ; OrnDesc = λ ℓs → algODᵈ (UPDataD.Desc D ℓs) (X ℓs) alg }