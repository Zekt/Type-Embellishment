{-# OPTIONS --safe #-}

module Generics.Safe.Ornament.Algebraic where

open import Prelude
open import Prelude.List as List
open import Generics.Safe.Description
open import Generics.Safe.Algebra
open import Generics.Safe.Ornament.Description
open Generics.Safe.Ornament.Description.ODFunctor

private variable
  rb : RecB
  cb : ConB
  cbs : ConBs

algODʳ : {I : Set ℓⁱ} (D : RecD I rb)
         (X : I → Set ℓ) (xs : ⟦ D ⟧ʳ X) → RecOD (Σ I X) fst D
algODʳ (ι i  ) X x  = ι (_ , x) refl
algODʳ (π A D) X xs = π λ a → algODʳ (D a) X (xs a)

algConB : Level → ConB → ConB
algConB ℓ []            = []
algConB ℓ (inl ℓ' ∷ cb) = inl ℓ' ∷ algConB ℓ cb
algConB ℓ (inr rb ∷ cb) = inl (max-ℓ rb ⊔ ℓ) ∷ inr rb ∷ algConB ℓ cb

algODᶜ : {I : Set ℓⁱ} (D : ConD I cb) (X : I → Set ℓ)
       → Algᶜ D X → ConOD (Σ I X) fst D (algConB ℓ cb)
algODᶜ (ι i  ) X f = ι (_ , f refl) refl
algODᶜ (σ A D) X f = σ λ a → algODᶜ (D a) X λ xs → f (a , xs)
algODᶜ (ρ D E) X f = Δ (⟦ D ⟧ʳ X) λ xs →
                     ρ (algODʳ D X xs) (algODᶜ E X (λ xs' → f (xs , xs')))

algODᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) (X : I → Set ℓ)
        → Algᶜˢ D X → ConODs (Σ I X) fst D (List.map (algConB ℓ) cbs)
algODᶜˢ []       X f = []
algODᶜˢ (D ∷ Ds) X f = algODᶜ  D  X (λ xs → f (inl xs))
                   ∷ ∺ algODᶜˢ Ds X (λ xs → f (inr xs))

algODᵖᵈ : (D : PDataD) (X : Carrierᵖᵈ D ℓ) → Algᵖᵈ D X → PDataOD D
algODᵖᵈ {ℓ} D X f = record
  { level  = PDataD.level D ⊔ hasCon? ℓ (PDataD.struct D)
  ; level-pre-fixed-point = pfp (PDataD.ilevel D) (PDataD.level D) (PDataD.struct D)
                                (PDataD.level-pre-fixed-point D)
  ; Param  = PDataD.Param D
  ; param  = id
  ; Index  = λ p → snoc (PDataD.Index D p) (X p)
  ; index  = λ _ → fst ∘ snoc-proj
  ; applyP = λ p → imapᶜˢ snoc-inj (fst ∘ snoc-proj) (λ p → cong fst (snoc-proj-inj p))
                      (algODᶜˢ (PDataD.applyP D p) (X p) f)
  }
  where
    algConB-lemma₀ : (g : ConB → Level) → (∀ cb → g (algConB ℓ cb) ≡ g cb) →
                     ∀ cbs → maxMap g (List.map (algConB ℓ) cbs) ≡ maxMap g cbs
    algConB-lemma₀ g eq cbs =
      begin
        maxMap g (List.map (algConB ℓ) cbs)
          ≡⟨⟩
        max-ℓ (List.map g (List.map (algConB ℓ) cbs))
          ≡⟨ cong max-ℓ (sym (map-comp g (algConB ℓ) cbs)) ⟩
        max-ℓ (List.map (g ∘ algConB ℓ) cbs)
          ≡⟨ cong max-ℓ (map-cong (g ∘ algConB ℓ) g eq cbs) ⟩
        max-ℓ (List.map g cbs)
          ≡⟨⟩
        maxMap g cbs
      ∎ where open ≡-Reasoning

    algConB-lemma₁ : ∀ cb → max-π (algConB ℓ cb) ≡ max-π cb
    algConB-lemma₁ []            = refl
    algConB-lemma₁ (inl ℓ' ∷ cb) = algConB-lemma₁ cb
    algConB-lemma₁ (inr rb ∷ cb) = cong (max-ℓ rb ⊔_) (algConB-lemma₁ cb)

    algConB-lemma₂ : ∀ cb → max-σ (algConB ℓ cb) ≡ max-π cb ⊔ max-σ cb ⊔ hasRec? ℓ cb
    algConB-lemma₂ []            = refl
    algConB-lemma₂ (inl ℓ' ∷ cb) = cong (ℓ' ⊔_) (algConB-lemma₂ cb)
    algConB-lemma₂ (inr rb ∷ cb) = cong (ℓ ⊔ max-ℓ rb ⊔_) (algConB-lemma₂ cb)

    algConB-lemma₃ : ∀ cbs → maxMap max-σ (List.map (algConB ℓ) cbs)
                           ≡ maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ maxMap (hasRec? ℓ) cbs
    algConB-lemma₃ []         = refl
    algConB-lemma₃ (cb ∷ cbs) = cong₂ _⊔_ (algConB-lemma₂ cb) (algConB-lemma₃ cbs)

    algConB-lemma₄ : ∀ ℓ' cb → hasRec? ℓ' (algConB ℓ cb) ≡ hasRec? ℓ' cb
    algConB-lemma₄ ℓ' []             = refl
    algConB-lemma₄ ℓ' (inl ℓ'' ∷ cb) = algConB-lemma₄ ℓ' cb
    algConB-lemma₄ ℓ' (inr rb  ∷ cb) = cong (ℓ' ⊔_) (algConB-lemma₄ ℓ' cb)

    algConB-lemma₅ : ∀ ℓ' cbs → hasCon? ℓ' (List.map (algConB ℓ) cbs) ≡ hasCon? ℓ' cbs
    algConB-lemma₅ ℓ' []         = refl
    algConB-lemma₅ ℓ' (cb ∷ cbs) = cong (ℓ' ⊔_) (algConB-lemma₅ ℓ' cbs)

    pfp : (ℓⁱ ℓᵖᵈ : Level) (cbs : ConBs)
        → maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔
          maxMap (hasRec? ℓᵖᵈ) cbs ⊔ hasCon? ℓⁱ cbs ⊔ ℓᵖᵈ ≡ ℓᵖᵈ
        → maxMap max-π (List.map (algConB ℓ) cbs) ⊔
          maxMap max-σ (List.map (algConB ℓ) cbs) ⊔
          maxMap (hasRec? (ℓᵖᵈ ⊔ hasCon? ℓ cbs)) (List.map (algConB ℓ) cbs) ⊔
          hasCon? (ℓ ⊔ ℓⁱ) (List.map (algConB ℓ) cbs) ⊔
          ℓᵖᵈ ⊔ hasCon? ℓ cbs ≡ ℓᵖᵈ ⊔ hasCon? ℓ cbs
    pfp ℓⁱ ℓᵖᵈ cbs pfp' =
      begin
        maxMap max-π (List.map (algConB ℓ) cbs) ⊔
        maxMap max-σ (List.map (algConB ℓ) cbs) ⊔
        maxMap (hasRec? (ℓᵖᵈ ⊔ hasCon? ℓ cbs)) (List.map (algConB ℓ) cbs) ⊔
        hasCon? (ℓ ⊔ ℓⁱ) (List.map (algConB ℓ) cbs) ⊔
        ℓᵖᵈ ⊔ hasCon? ℓ cbs
          ≡⟨ -- eliminating algConB
             cong (ℓᵖᵈ ⊔ hasCon? ℓ cbs ⊔_) (cong₂ _⊔_ (cong₂ _⊔_ (cong₂ _⊔_
            (algConB-lemma₀ max-π algConB-lemma₁ cbs)
            (algConB-lemma₃ cbs))
            (algConB-lemma₀ (hasRec? (ℓᵖᵈ ⊔ hasCon? ℓ cbs))
            (algConB-lemma₄ (ℓᵖᵈ ⊔ hasCon? ℓ cbs)) cbs))
            (algConB-lemma₅ (ℓ ⊔ ℓⁱ) cbs)) ⟩
        maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ maxMap (hasRec? ℓ) cbs ⊔
        maxMap (hasRec? (ℓᵖᵈ ⊔ hasCon? ℓ cbs)) cbs ⊔
        hasCon? (ℓ ⊔ ℓⁱ) cbs ⊔ ℓᵖᵈ ⊔ hasCon? ℓ cbs
          ≡⟨ -- distributing over _⊔_
             cong (maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔
                   maxMap (hasRec? ℓ) cbs ⊔ ℓᵖᵈ ⊔ hasCon? ℓ cbs ⊔_) (cong₂ _⊔_
            (trans (cong max-ℓ
                      (map-cong (hasRec? (ℓᵖᵈ ⊔ hasCon? ℓ cbs))
                                (λ cb → hasRec? ℓᵖᵈ cb ⊔ hasRec? (hasCon? ℓ cbs) cb)
                                (hasRec?-dist-⊔ ℓᵖᵈ (hasCon? ℓ cbs)) cbs))
               (maxMap-dist-⊔ (hasRec? ℓᵖᵈ) (hasRec? (hasCon? ℓ cbs)) cbs))
            (hasCon?-dist-⊔ ℓ ℓⁱ cbs)) ⟩
        maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ maxMap (hasRec? ℓ) cbs ⊔
        maxMap (hasRec? ℓᵖᵈ) cbs ⊔ maxMap (hasRec? (hasCon? ℓ cbs)) cbs ⊔
        hasCon? ℓⁱ cbs ⊔ ℓᵖᵈ ⊔ hasCon? ℓ cbs
          ≡⟨ -- original pre-fixed-point & level-conditionals
             cong₂ _⊔_ pfp' (cong₂ _⊔_
            (maxMap-hasRec?≤hasCon? ℓ cbs)
            (maxMap-bound (hasRec? (hasCon? ℓ cbs)) (hasCon? ℓ cbs)
                          (hasRec?-bound (hasCon? ℓ cbs)) cbs)) ⟩
        ℓᵖᵈ ⊔ hasCon? ℓ cbs
      ∎ where open ≡-Reasoning

algODᵈ : (D : DataD) {ℓf : DataD.Levels D → Level} (X : Carrierᵈ D ℓf)
       → Algᵈ D X → DataOD D
algODᵈ D X f = record
  { #levels = DataD.#levels D
  ; levels  = id
  ; applyL  = λ ℓs → algODᵖᵈ (DataD.applyL D ℓs) (X ℓs) f }
