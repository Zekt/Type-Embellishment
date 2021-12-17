{-# OPTIONS --safe #-}

module Generics.Safe.Ornament.Algebraic where

open import Prelude
open import Prelude.List as List
open import Generics.Safe.Telescope
open import Generics.Safe.Description
open import Generics.Safe.Algebra
open import Generics.Safe.Ornament
open import Generics.Safe.Ornament.Description
open Generics.Safe.Ornament.Description.ODFunctor

private variable
  rb  : RecB
  cb  : ConB
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

algODᵖᵈ : (D : PDataD) → (∀ ps → Algebraᵖᵈ D ps ℓ) → PDataOD D
algODᵖᵈ {ℓ} D alg = let X = Algebraᵖᵈ.Carrier ∘ alg in record
  { alevel  = PDataD.alevel D
  ; level-pre-fixed-point = pfp (PDataD.ilevel D) (PDataD.dlevel D) (PDataD.struct D)
                                (PDataD.level-pre-fixed-point D)
  ; ParamOD = ε
  ; IndexOD = λ ps → ▷ ε (X ps)
  ; applyP  = λ ps → imapODᶜˢ snocᵗ-inj (fst ∘ snocᵗ-proj) (cong fst ∘ snocᵗ-proj-inj)
                       (algODᶜˢ (PDataD.applyP D ps) (X ps) (Algebraᵖᵈ.apply (alg ps)))
  }
  where
    algConB-lemma₀ : ∀ cb → max-π (algConB ℓ cb) ≡ max-π cb
    algConB-lemma₀ []            = refl
    algConB-lemma₀ (inl ℓ' ∷ cb) = algConB-lemma₀ cb
    algConB-lemma₀ (inr rb ∷ cb) = cong (max-ℓ rb ⊔_) (algConB-lemma₀ cb)

    algConB-lemma₁ : ∀ cbs → maxMap max-π (List.map (algConB ℓ) cbs) ≡ maxMap max-π cbs
    algConB-lemma₁ []         = refl
    algConB-lemma₁ (cb ∷ cbs) = cong₂ _⊔_ (algConB-lemma₀ cb) (algConB-lemma₁ cbs)

    algConB-lemma₂ : ∀ cb → max-σ (algConB ℓ cb) ≡ max-π cb ⊔ max-σ cb ⊔ hasRec? ℓ cb
    algConB-lemma₂ []            = refl
    algConB-lemma₂ (inl ℓ' ∷ cb) = cong (ℓ' ⊔_) (algConB-lemma₂ cb)
    algConB-lemma₂ (inr rb ∷ cb) = cong (ℓ ⊔ max-ℓ rb ⊔_) (algConB-lemma₂ cb)

    algConB-lemma₃ : ∀ cbs → maxMap max-σ (List.map (algConB ℓ) cbs)
                           ≡ maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ maxMap (hasRec? ℓ) cbs
    algConB-lemma₃ []         = refl
    algConB-lemma₃ (cb ∷ cbs) = cong₂ _⊔_ (algConB-lemma₂ cb) (algConB-lemma₃ cbs)

    pfp : (ℓⁱ ℓᵃ : Level) (cbs : ConBs)
        → maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ maxMap (hasRec? (ℓᵃ ⊔ ℓⁱ)) cbs ⊔
          hasCon? ℓⁱ cbs ⊔ ℓᵃ ⊔ ℓⁱ ≡ ℓᵃ ⊔ ℓⁱ
        → maxMap max-π (List.map (algConB ℓ) cbs) ⊔
          maxMap max-σ (List.map (algConB ℓ) cbs) ⊔
          maxMap (hasRec? (ℓᵃ ⊔ ℓⁱ ⊔ ℓ)) (List.map (algConB ℓ) cbs) ⊔
          hasCon? (ℓⁱ ⊔ ℓ) (List.map (algConB ℓ) cbs) ⊔ ℓᵃ ⊔ ℓⁱ ⊔ ℓ ≡ ℓᵃ ⊔ ℓⁱ ⊔ ℓ
    pfp ℓⁱ ℓᵃ cbs pfp' =
      begin
        maxMap max-π (List.map (algConB ℓ) cbs) ⊔
        maxMap max-σ (List.map (algConB ℓ) cbs) ⊔
        maxMap (hasRec? (ℓᵃ ⊔ ℓⁱ ⊔ ℓ)) (List.map (algConB ℓ) cbs) ⊔
        hasCon? (ℓⁱ ⊔ ℓ) (List.map (algConB ℓ) cbs) ⊔ ℓᵃ ⊔ ℓⁱ ⊔ ℓ
          ≡⟨ -- eliminating algConB; boundedness of level-conditionals
            (let cbs' = List.map (algConB ℓ) cbs
             in  cong₂ _⊔_ (cong₂ _⊔_ (cong₂ _⊔_
                (algConB-lemma₁ cbs)
                (algConB-lemma₃ cbs))
                (maxMap-bound (hasRec? (ℓᵃ ⊔ ℓⁱ ⊔ ℓ)) _
                              (hasRec?-bound (ℓᵃ ⊔ ℓⁱ ⊔ ℓ)) cbs'))
                (hasCon?-bound (ℓⁱ ⊔ ℓ) cbs')) ⟩
        maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ maxMap (hasRec? ℓ) cbs ⊔ ℓᵃ ⊔ ℓ ⊔ ℓⁱ
          ≡⟨ -- boundedness of level-conditionals
             cong (maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔_) (cong₂ _⊔_ (cong₂ _⊔_
            (maxMap-bound (hasRec? ℓ) _ (hasRec?-bound ℓ) cbs)
            (sym (maxMap-bound (hasRec? (ℓᵃ ⊔ ℓⁱ)) _ (hasRec?-bound (ℓᵃ ⊔ ℓⁱ)) cbs)))
            (sym (hasCon?-bound ℓⁱ cbs))) ⟩
        maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ maxMap (hasRec? (ℓᵃ ⊔ ℓⁱ)) cbs ⊔
        hasCon? ℓⁱ cbs ⊔ ℓᵃ ⊔ ℓⁱ ⊔ ℓ
          ≡⟨ cong (ℓ ⊔_) pfp' ⟩
        ℓᵃ ⊔ ℓⁱ ⊔ ℓ
      ∎ where open ≡-Reasoning

algODᵈ : (D : DataD) → (∀ ℓs ps → Algebraᵈ D ℓs ps ℓ) → DataOD D
algODᵈ D alg = record
  { #levels = DataD.#levels D
  ; LevelO  = ε
  ; applyL  = λ ℓs → algODᵖᵈ (DataD.applyL D ℓs) (alg ℓs) }
