{-# OPTIONS --safe --with-K #-}

module Generics.SimpleContainer.All where

open import Prelude
open import Generics.Telescope
open import Generics.Description
open import Generics.Recursion
open import Generics.Ornament
open import Generics.Ornament.Description
open import Generics.Ornament.Algebraic
open import Generics.SimpleContainer

private variable
  cb  : ConB
  cbs : ConBs

PredODᶜ : {I : Set ℓⁱ} (D : ConD I cb) (El : Set ℓᵉ) (P : El → Set ℓ)
          (sb : SCᵇ cb) → SCᶜ D sb El
        → ConOD I id D (scConB ℓ cb sb)
PredODᶜ (ι i  ) El P _            sc = ι i refl
PredODᶜ (σ A D) El P (false ∷ sb) sc = σ λ a → PredODᶜ (D a) El P sb (sc a)
PredODᶜ (σ A D) .A P (true  ∷ sb) (refl ,ωω sc) =
  σ λ a → Δ (P a) λ _ → PredODᶜ (D a) A P sb (sc a)
PredODᶜ (ρ D E) El P (_     ∷ sb) sc = ρ (idRecOD D) (PredODᶜ E El P sb sc)

PredODᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) (El : Set ℓᵉ) (P : El → Set ℓ)
           (sb : All SCᵇ cbs) → SCᶜˢ D sb El
         → ConODs I id D (map (uncurry (scConB ℓ)) (allToList sb))
PredODᶜˢ []       El P []         _            = []
PredODᶜˢ (D ∷ Ds) El P (sb ∷ sbs) (sc ,ωω scs) = PredODᶜ  D  El P sb  sc
                                             ∷ ∺ PredODᶜˢ Ds El P sbs scs

module _ (ℓ : Level) where

  scConB-lemma₀ : ∀ cb s → max-π (scConB ℓ cb s) ≡ max-π cb
  scConB-lemma₀ [] _ = refl
  scConB-lemma₀ (inl ℓ' ∷ cb) (false ∷ s) = scConB-lemma₀ cb s
  scConB-lemma₀ (inl ℓ' ∷ cb) (true  ∷ s) = scConB-lemma₀ cb s
  scConB-lemma₀ (inr rb ∷ cb) (_     ∷ s) = cong (max-ℓ rb ⊔_) (scConB-lemma₀ cb s)

  scConB-lemma₁ : ∀ cbs (ss : All SCᵇ cbs)
                → maxMap max-π (map (uncurry (scConB ℓ)) (allToList ss))
                ≡ maxMap max-π cbs
  scConB-lemma₁ [] [] = refl
  scConB-lemma₁ (cb ∷ cbs) (s ∷ ss) = cong₂ _⊔_ (scConB-lemma₀ cb s) (scConB-lemma₁ cbs ss)

  scConB-lemma₂ : ∀ cb s → max-σ (scConB ℓ cb s) ≡ max-σ cb ⊔ hasEl? ℓ cb s
  scConB-lemma₂ [] _ = refl
  scConB-lemma₂ (inl ℓ' ∷ cb) (false ∷ s) = cong (ℓ' ⊔_) (scConB-lemma₂ cb s)
  scConB-lemma₂ (inl ℓ' ∷ cb) (true  ∷ s) = cong (ℓ' ⊔ ℓ ⊔_) (scConB-lemma₂ cb s)
  scConB-lemma₂ (inr rb ∷ cb) (_     ∷ s) = scConB-lemma₂ cb s

  scConB-lemma₃ : ∀ cbs (ss : All SCᵇ cbs)
                → maxMap max-σ (map (uncurry (scConB ℓ)) (allToList ss))
                ≡ maxMap max-σ cbs ⊔ maxMap (uncurry (hasEl? ℓ)) (allToList ss)
  scConB-lemma₃ [] [] = refl
  scConB-lemma₃ (cb ∷ cbs) (s ∷ ss) = cong₂ _⊔_ (scConB-lemma₂ cb s) (scConB-lemma₃ cbs ss)

  PredOD-pfp-lemma :
      (ℓⁱ ℓᵃ : Level) (cbs : ConBs) (ss : All SCᵇ cbs)
    → maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔
      maxMap (hasRec? (ℓᵃ ⊔ ℓⁱ)) cbs ⊔ hasCon? ℓⁱ cbs ⊔ ℓᵃ ⊔ ℓⁱ
    ≡ ℓᵃ ⊔ ℓⁱ
    → maxMap max-π (map (uncurry (scConB ℓ)) (allToList ss)) ⊔
      maxMap max-σ (map (uncurry (scConB ℓ)) (allToList ss)) ⊔
      maxMap (hasRec? (ℓᵃ ⊔ maxMap (uncurry (hasEl? ℓ)) (allToList ss) ⊔ ℓⁱ))
             (map (uncurry (scConB ℓ)) (allToList ss)) ⊔
      hasCon? ℓⁱ (map (uncurry (scConB ℓ)) (allToList ss)) ⊔
      ℓᵃ ⊔ maxMap (uncurry (hasEl? ℓ)) (allToList ss) ⊔ ℓⁱ
    ≡ ℓᵃ ⊔ maxMap (uncurry (hasEl? ℓ)) (allToList ss) ⊔ ℓⁱ
  PredOD-pfp-lemma ℓⁱ ℓᵃ cbs ss pfp =
    let ℓᵉ   = maxMap (uncurry (hasEl? ℓ)) (allToList ss)
        cbs' = map (uncurry (scConB ℓ)) (allToList ss) in
    begin
      maxMap max-π cbs' ⊔ maxMap max-σ cbs' ⊔
      maxMap (hasRec? (ℓᵃ ⊔ ℓᵉ ⊔ ℓⁱ)) cbs' ⊔ hasCon? ℓⁱ cbs' ⊔
      ℓᵃ ⊔ ℓᵉ ⊔ ℓⁱ
        ≡⟨ -- eliminating algConB; boundedness of level-conditionals
           cong₂ _⊔_ (cong₂ _⊔_ (cong₂ _⊔_
          (scConB-lemma₁ cbs ss) (scConB-lemma₃ cbs ss))
          (maxMap-bound (hasRec? (ℓᵃ ⊔ ℓᵉ ⊔ ℓⁱ)) _ (hasRec?-bound (ℓᵃ ⊔ ℓᵉ ⊔ ℓⁱ)) cbs'))
          (hasCon?-bound ℓⁱ cbs') ⟩  --
      maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ ℓᵃ ⊔ ℓᵉ ⊔ ℓⁱ
        ≡⟨ -- boundedness of level-conditionals
           cong (maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ ℓᵉ ⊔_) (cong₂ _⊔_
          (sym (maxMap-bound (hasRec? (ℓᵃ ⊔ ℓⁱ)) _ (hasRec?-bound (ℓᵃ ⊔ ℓⁱ)) cbs))
          (sym (hasCon?-bound ℓⁱ cbs))) ⟩
      maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔
      maxMap (hasRec? (ℓᵃ ⊔ ℓⁱ)) cbs ⊔ hasCon? ℓⁱ cbs ⊔
      ℓᵃ ⊔ ℓᵉ ⊔ ℓⁱ
        ≡⟨ cong (ℓᵉ ⊔_) pfp ⟩
      ℓᵃ ⊔ ℓᵉ ⊔ ℓⁱ
    ∎ where open ≡-Reasoning

PredODᵖᵈ : (D : PDataD) → SC D → Level → PDataOD D
PredODᵖᵈ D S ℓ = record
  { alevel = PDataD.alevel D ⊔ maxMap (uncurry (hasEl? ℓ)) (allToList (SC.pos S))
  ; level-pre-fixed-point = PredOD-pfp-lemma ℓ (PDataD.ilevel D) (PDataD.alevel D)
      (PDataD.struct D) (SC.pos S) (PDataD.level-pre-fixed-point D)
  ; Param = [[ ps ∶ PDataD.Param D ]] [ P ∶ (SC.El S ps → Set ℓ) ] []
  ; param = fst
  ; Index = λ (ps , _) → PDataD.Index D ps
  ; index = λ _ → id
  ; applyP = λ (ps , P , _) →
      PredODᶜˢ (PDataD.applyP D ps) (SC.El S ps) P (SC.pos S) (SC.coe S ps) }

PredOD : (D : DataD) → SCᵈ D → DataOD D
PredOD D S = record
  { #levels = suc (DataD.#levels D)
  ; level   = snd
  ; applyL  = λ (ℓ , ℓs) → PredODᵖᵈ (DataD.applyL D ℓs) (S ℓs) ℓ }

AllOD : ∀ {D N} → DataC D N → (S : SCᵈ D) → ∀ {N'} → DataC ⌊ PredOD D S ⌋ᵈ N'
      → DataOD ⌊ PredOD D S ⌋ᵈ
AllOD {D} C S C' = AlgOD (forget C' C ⌈ PredOD D S ⌉ᵈ)
