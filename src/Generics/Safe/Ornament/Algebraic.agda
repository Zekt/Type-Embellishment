{-# OPTIONS --safe #-}

module Generics.Safe.Ornament.Algebraic where

open import Prelude
open import Generics.Safe.Description
open import Generics.Safe.Algebra
open import Generics.Safe.Ornament.Description

private
  variable
    cρ : ℕ
    cρs : List ℕ

algODʳ : {I : Set ℓⁱ} (D : RecD I ℓʳ)
         (X : I → Set ℓ) (xs : ⟦ D ⟧ʳ X) → RecOD (Σ I X) fst D
algODʳ (ι i  ) X x  = ι (_ , x) refl
algODʳ (π A D) X xs = π λ a → algODʳ (D a) X (xs a)

algODᶜ : {I : Set ℓⁱ} (D : ConD I ℓʳ ℓᵃ cρ) (X : I → Set ℓ)
       → Algᶜ D X → ConOD (Σ I X) fst D (ℓʳ ⊔ ℓᵃ ⊔ lcond cρ ℓ)
algODᶜ (ι i  ) X f = ι (_ , f refl) refl
algODᶜ (ρ D E) X f = Δ (⟦ D ⟧ʳ X) λ xs →
                     ρ (algODʳ D X xs) (algODᶜ E X (λ xs' → f (xs , xs')))
algODᶜ (σ A D) X f = σ λ a → algODᶜ (D a) X λ xs → f (a , xs)

algODᶜˢ : {I : Set ℓⁱ} (D : ConDs I ℓʳ ℓᵃ cρs) (X : I → Set ℓ)
        → Algᶜˢ D X → ConODs (Σ I X) fst D ℓʳ (ℓʳ ⊔ ℓᵃ ⊔ lconds cρs ℓ) cρs
algODᶜˢ ∅        X f = ∅
algODᶜˢ (D ◁ Ds) X f = algODᶜ  D  X (λ xs → f (inl xs))
                   ◁ ◂ algODᶜˢ Ds X (λ xs → f (inr xs))

algODᵈ : (D : DataD) (X : Carrierᵈ D ℓ) → Algᵈ D X → DataOD D
algODᵈ {ℓ} D X f = record
  { level = DataD.level D ⊔ lcond (length (DataD.recCounts D)) ℓ
                          ⊔ lconds        (DataD.recCounts D)  ℓ
  ; level-pre-fixed-point = pfp (DataD.recCounts D)
                                (DataD.rlevel D) (DataD.alevel D) (DataD.ilevel D)
                                (DataD.level D)
                                (DataD.level-pre-fixed-point D)
  ; Param = DataD.Param D
  ; param = id
  ; Index = λ p → DataD.Index D p ▷ X p
  ; index = λ _ → fst
  ; OrnDesc = λ p → algODᶜˢ (DataD.Desc D p) (X p) f
  }
  where
  pfp : (ns : List ℕ) (ℓʳ ℓᵃ ℓⁱ ℓ' : Level)
      → ℓʳ ⊔ ℓᵃ ⊔ ℓ' ⊔ lcond (length ns) ℓⁱ ⊔ lconds ns ℓ' ≡ ℓ'
      → ℓʳ ⊔ ℓᵃ ⊔ ℓ' ⊔ lcond (length ns) ℓ ⊔ lcond (length ns) (ℓⁱ ⊔ ℓ)
        ⊔ lconds ns ℓ ⊔ lconds ns (ℓ' ⊔ lcond (length ns) ℓ ⊔ lconds ns ℓ)
      ≡ ℓ' ⊔ lcond (length ns) ℓ ⊔ lconds ns ℓ
  pfp ns ℓʳ ℓᵃ ℓⁱ ℓ' eq =
    trans (cong ((ℓʳ ⊔ ℓᵃ) ⊔_)
             (cong₂ _⊔_ (sym (lconds-upper-bound ns ℓ'))
             (cong₂ _⊔_ (lcond-preserves-⊔ (length ns) ℓ ℓⁱ)
                        (lconds-upper-bound ns
                           (ℓ' ⊔ lcond (length ns) ℓ ⊔ lconds ns ℓ)))))
          (cong ((lcond (length ns) ℓ ⊔ lconds ns ℓ) ⊔_) eq)

algODᵘᵖᵈ : (D : UPDataD) (X : Carrierᵘᵖᵈ D ℓ) → Algᵘᵖᵈ D X → UPDataOD D
algODᵘᵖᵈ D X f = record
  { #levels = UPDataD.#levels D
  ; levels  = id
  ; OrnDesc = λ ℓs → algODᵈ (UPDataD.Desc D ℓs) (X ℓs) f }