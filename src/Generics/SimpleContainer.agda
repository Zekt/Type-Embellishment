{-# OPTIONS --safe --with-K #-}

open import Prelude

module Generics.SimpleContainer where
open import Generics.Telescope
open import Generics.Description
open import Generics.Algebra
open import Generics.Recursion
open import Generics.Ornament
open import Generics.Ornament.Description

private variable
  cb  : ConB
  cbs : ConBs

SCᵇ : ConB → Set
SCᵇ [] = ⊤
SCᵇ (inl _ ∷ cb) = Bool × SCᵇ cb
SCᵇ (inr _ ∷ cb) = SCᵇ cb

scConB : Level → (cb : ConB) → SCᵇ cb → ConB
scConB ℓ' [] _ = []
scConB ℓ' (inl ℓ  ∷ cb) (false , s) = inl ℓ ∷ scConB ℓ' cb s
scConB ℓ' (inl ℓ  ∷ cb) (true  , s) = inl ℓ ∷ inl ℓ' ∷ scConB ℓ' cb s
scConB ℓ' (inr rb ∷ cb) s = inr rb ∷ scConB ℓ' cb s

hasEl? : Level → (cb : ConB) → SCᵇ cb → Level
hasEl? ℓ' [] _ = lzero
hasEl? ℓ' (inl _ ∷ cb) (false , s) = hasEl? ℓ' cb s
hasEl? ℓ' (inl _ ∷ cb) (true  , s) = ℓ' ⊔ hasEl? ℓ' cb s
hasEl? ℓ' (inr _ ∷ cb) s = hasEl? ℓ' cb s

SCᶜ : {I : Set ℓⁱ} (D : ConD I cb) → SCᵇ cb → Set ℓ → Setω
SCᶜ (ι i  ) s X = Liftω ⊤
SCᶜ (σ A D) (false , s) X = (a : A) → SCᶜ (D a) s X
SCᶜ (σ A D) (true  , s) X = Σωω[ _ ∈ (_ ,ℓ A) ≡ω ((_ ,ℓ X) ⦂ω Σℓ[ ℓ' ] Set ℓ') ]
                           ((a : A) → SCᶜ (D a) s X)
SCᶜ (ρ D E) s X = SCᶜ E s X

SCᶜˢ : {I : Set ℓⁱ} → ConDs I cbs → All SCᵇ cbs → Set ℓ → Setω
SCᶜˢ []            ss  X = Liftω ⊤
SCᶜˢ (D ∷ Ds) (s ∷ ss) X = Σωω[ _ ∈ SCᶜ D s X ] SCᶜˢ Ds ss X

record SC (D : PDataD) : Setω where
  field
    {elevel} : Level
    El  : ⟦ PDataD.Param D ⟧ᵗ → Set elevel
    pos : All SCᵇ (PDataD.struct D)
    coe : (ps : ⟦ PDataD.Param D ⟧ᵗ) → SCᶜˢ (PDataD.applyP D ps) pos (El ps)

SCᵈ : DataD → Setω
SCᵈ D = ∀ ℓs → SC (DataD.applyL D ℓs)

PredODᶜ : {I : Set ℓⁱ} (D : ConD I cb) (El : Set ℓ) (P : El → Set ℓ')
          (sb : SCᵇ cb) → SCᶜ D sb El
        → ConOD I id D (scConB ℓ' cb sb)
PredODᶜ (ι i  ) El P sb sc = ι i refl
PredODᶜ (σ A D) El P (false , sb) sc = σ λ a → PredODᶜ (D a) El P sb (sc a)
PredODᶜ (σ A D) .A P (true  , sb) (refl ,ωω sc) =
  σ λ a → Δ (P a) λ _ → PredODᶜ (D a) A P sb (sc a)
PredODᶜ (ρ D E) El P sb sc = ρ (idRecOD D) (PredODᶜ E El P sb sc)

PredODᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) (El : Set ℓ) (P : El → Set ℓ')
           (sb : All SCᵇ cbs) → SCᶜˢ D sb El
         → ConODs I id D (map (uncurry (scConB ℓ')) (allToList sb))
PredODᶜˢ []       El P []         _            = []
PredODᶜˢ (D ∷ Ds) El P (sb ∷ sbs) (sc ,ωω scs) = PredODᶜ  D  El P sb  sc
                                             ∷ ∺ PredODᶜˢ Ds El P sbs scs

module _ (ℓ' : Level) where

  scConB-lemma₀ : ∀ cb s → max-π (scConB ℓ' cb s) ≡ max-π cb
  scConB-lemma₀ [] _ = refl
  scConB-lemma₀ (inl ℓ  ∷ cb) (false , s) = scConB-lemma₀ cb s
  scConB-lemma₀ (inl ℓ  ∷ cb) (true  , s) = scConB-lemma₀ cb s
  scConB-lemma₀ (inr rb ∷ cb) s = cong (max-ℓ rb ⊔_) (scConB-lemma₀ cb s)

  scConB-lemma₁ : ∀ cbs (ss : All SCᵇ cbs)
                → maxMap max-π (map (uncurry (scConB ℓ')) (allToList ss))
                ≡ maxMap max-π cbs
  scConB-lemma₁ [] [] = refl
  scConB-lemma₁ (cb ∷ cbs) (s ∷ ss) = cong₂ _⊔_ (scConB-lemma₀ cb s) (scConB-lemma₁ cbs ss)

  scConB-lemma₂ : ∀ cb s → max-σ (scConB ℓ' cb s) ≡ max-σ cb ⊔ hasEl? ℓ' cb s
  scConB-lemma₂ [] _ = refl
  scConB-lemma₂ (inl ℓ  ∷ cb) (false , s) = cong (ℓ ⊔_) (scConB-lemma₂ cb s)
  scConB-lemma₂ (inl ℓ  ∷ cb) (true  , s) = cong (ℓ ⊔ ℓ' ⊔_) (scConB-lemma₂ cb s)
  scConB-lemma₂ (inr rb ∷ cb) s = scConB-lemma₂ cb s

  scConB-lemma₃ : ∀ cbs (ss : All SCᵇ cbs)
                → maxMap max-σ (map (uncurry (scConB ℓ')) (allToList ss))
                ≡ maxMap max-σ cbs ⊔ maxMap (uncurry (hasEl? ℓ')) (allToList ss)
  scConB-lemma₃ [] [] = refl
  scConB-lemma₃ (cb ∷ cbs) (s ∷ ss) = cong₂ _⊔_ (scConB-lemma₂ cb s) (scConB-lemma₃ cbs ss)

  PredOD-pfp-lemma :
      (ℓⁱ ℓᵃ : Level) (cbs : ConBs) (ss : All SCᵇ cbs)
    → maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔
      maxMap (hasRec? (ℓᵃ ⊔ ℓⁱ)) cbs ⊔ hasCon? ℓⁱ cbs ⊔ ℓᵃ ⊔ ℓⁱ
    ≡ ℓᵃ ⊔ ℓⁱ
    → maxMap max-π (map (uncurry (scConB ℓ')) (allToList ss)) ⊔
      maxMap max-σ (map (uncurry (scConB ℓ')) (allToList ss)) ⊔
      maxMap (hasRec? (ℓᵃ ⊔ maxMap (uncurry (hasEl? ℓ')) (allToList ss) ⊔ ℓⁱ))
             (map (uncurry (scConB ℓ')) (allToList ss)) ⊔
      hasCon? ℓⁱ (map (uncurry (scConB ℓ')) (allToList ss)) ⊔
      ℓᵃ ⊔ maxMap (uncurry (hasEl? ℓ')) (allToList ss) ⊔ ℓⁱ
    ≡ ℓᵃ ⊔ maxMap (uncurry (hasEl? ℓ')) (allToList ss) ⊔ ℓⁱ
  PredOD-pfp-lemma ℓⁱ ℓᵃ cbs ss pfp' =
    let ℓᵉ   = maxMap (uncurry (hasEl? ℓ')) (allToList ss)
        cbs' = map (uncurry (scConB ℓ')) (allToList ss) in
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
        ≡⟨ cong (ℓᵉ ⊔_) pfp' ⟩
      ℓᵃ ⊔ ℓᵉ ⊔ ℓⁱ
    ∎ where open ≡-Reasoning

PredODᵖᵈ : (D : PDataD) → SC D → Level → PDataOD D
PredODᵖᵈ D S ℓ' = record
  { alevel = PDataD.alevel D ⊔ maxMap (uncurry (hasEl? ℓ')) (allToList (SC.pos S))
  ; level-pre-fixed-point = PredOD-pfp-lemma ℓ' (PDataD.ilevel D) (PDataD.alevel D)
      (PDataD.struct D) (SC.pos S) (PDataD.level-pre-fixed-point D)
  ; Param = [[ ps ∶ PDataD.Param D ]] [ _ ∶ (SC.El S ps → Set ℓ') ] []
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
