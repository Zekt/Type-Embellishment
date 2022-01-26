{-# OPTIONS --safe --with-K #-}

module Generics.SimpleContainer where

open import Prelude
open import Prelude.Sum as Sum
open import Generics.Telescope
open import Generics.Description

private variable
  cb  : ConB
  cbs : ConBs

SCᵇ : ConB → Set
SCᵇ = All Sum.[ const Bool , const ⊤ ]

scConB : Level → (cb : ConB) → SCᵇ cb → ConB
scConB ℓ []            _           = []
scConB ℓ (inl ℓ' ∷ cb) (false ∷ s) = inl ℓ' ∷ scConB ℓ cb s
scConB ℓ (inl ℓ' ∷ cb) (true  ∷ s) = inl ℓ' ∷ inl ℓ ∷ scConB ℓ cb s
scConB ℓ (inr rb ∷ cb) (_     ∷ s) = inr rb ∷ scConB ℓ cb s

hasEl? : Level → (cb : ConB) → SCᵇ cb → Level
hasEl? ℓ []           _           = lzero
hasEl? ℓ (inl _ ∷ cb) (false ∷ s) = hasEl? ℓ cb s
hasEl? ℓ (inl _ ∷ cb) (true  ∷ s) = ℓ ⊔ hasEl? ℓ cb s
hasEl? ℓ (inr _ ∷ cb) (_     ∷ s) = hasEl? ℓ cb s

hasEl?-bound : (ℓ : Level) (cb : ConB) (sb : SCᵇ cb) {ℓ' : Level}
             → ℓ ⊑ ℓ' → hasEl? ℓ cb sb ⊑ ℓ'
hasEl?-bound ℓ []           []           ℓ⊑ℓ' = refl
hasEl?-bound ℓ (inl _ ∷ cb) (false ∷ sb) ℓ⊑ℓ' = hasEl?-bound ℓ cb sb ℓ⊑ℓ'
hasEl?-bound ℓ (inl _ ∷ cb) (true  ∷ sb) ℓ⊑ℓ' = trans (cong (ℓ ⊔_)
                                               (hasEl?-bound ℓ cb sb ℓ⊑ℓ')) ℓ⊑ℓ'
hasEl?-bound ℓ (inr _ ∷ cb) (_     ∷ sb) ℓ⊑ℓ' = hasEl?-bound ℓ cb sb ℓ⊑ℓ'

hasEl?-dist-⊔ : (ℓ ℓ' : Level) (cb : ConB) (sb : SCᵇ cb)
              → hasEl? (ℓ ⊔ ℓ') cb sb ≡ hasEl? ℓ cb sb ⊔ hasEl? ℓ' cb sb
hasEl?-dist-⊔ ℓ ℓ' []           []           = refl
hasEl?-dist-⊔ ℓ ℓ' (inl _ ∷ cb) (false ∷ sb) = hasEl?-dist-⊔ ℓ ℓ' cb sb
hasEl?-dist-⊔ ℓ ℓ' (inl _ ∷ cb) (true  ∷ sb) = cong (ℓ ⊔ ℓ' ⊔_) (hasEl?-dist-⊔ ℓ ℓ' cb sb)
hasEl?-dist-⊔ ℓ ℓ' (inr _ ∷ cb) (_     ∷ sb) = hasEl?-dist-⊔ ℓ ℓ' cb sb

SCᶜ : {I : Set ℓⁱ} (D : ConD I cb) → SCᵇ cb → Set ℓ → Setω
SCᶜ (ι i  ) _           X = Liftω ⊤
SCᶜ (σ A D) (false ∷ s) X = (a : A) → SCᶜ (D a) s X
SCᶜ (σ A D) (true  ∷ s) X = Σωω[ _ ∈ (_ ,ℓ A) ≡ω ((_ ,ℓ X) ⦂ω Σℓ[ ℓ ] Set ℓ) ]
                           ((a : A) → SCᶜ (D a) s X)
SCᶜ (ρ D E) (_     ∷ s) X = SCᶜ E s X

SCᶜˢ : {I : Set ℓⁱ} → ConDs I cbs → All SCᵇ cbs → Set ℓᵉ → Setω
SCᶜˢ []            ss  E = Liftω ⊤
SCᶜˢ (D ∷ Ds) (s ∷ ss) E = Σωω[ _ ∈ SCᶜ D s E ] SCᶜˢ Ds ss E

record SC (D : PDataD) : Setω where
  field
    {elevel} : Level
    El  : ⟦ PDataD.Param D ⟧ᵗ → Set elevel
    pos : All SCᵇ (PDataD.struct D)
    coe : (ps : ⟦ PDataD.Param D ⟧ᵗ) → SCᶜˢ (PDataD.applyP D ps) pos (El ps)

SCᵈ : DataD → Setω
SCᵈ D = ∀ {ℓs} → SC (DataD.applyL D ℓs)
