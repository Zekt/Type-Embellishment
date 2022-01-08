{-# OPTIONS --safe #-}

module Generics.Safe.Ornament.Algebraic where

open import Prelude
open import Prelude.List as List
open import Generics.Safe.Telescope; open ∀ℓ; open ∀ᵗ
open import Generics.Safe.Description
open import Generics.Safe.Algebra
open import Generics.Safe.Recursion
open import Generics.Safe.Ornament
open import Generics.Safe.Ornament.Description

private variable
  rb  : RecB
  cb  : ConB
  cbs : ConBs

algODʳ : {I : Set ℓⁱ} (D : RecD I rb)
         {X : I → Set ℓ} (xs : ⟦ D ⟧ʳ X) → RecOD (Σ[ i ∈ I ] X i × ⊤) fst D
algODʳ (ι i  ) x  = ι (_ , x , tt) refl
algODʳ (π A D) xs = π λ a → algODʳ (D a) (xs a)

algConB : Level → ConB → ConB
algConB ℓ []            = []
algConB ℓ (inl ℓ' ∷ cb) = inl ℓ' ∷ algConB ℓ cb
algConB ℓ (inr rb ∷ cb) = inl (max-ℓ rb ⊔ ℓ) ∷ inr rb ∷ algConB ℓ cb

algODᶜ : {I : Set ℓⁱ} (D : ConD I cb) {X : I → Set ℓ}
       → Algᶜ D X → ConOD (Σ[ i ∈ I ] X i × ⊤) fst D (algConB ℓ cb)
algODᶜ (ι i  ) f = ι (_ , f refl , tt) refl
algODᶜ (σ A D) f = σ λ a → algODᶜ (D a) λ xs → f (a , xs)
algODᶜ (ρ D E) f = Δ (⟦ D ⟧ʳ _) λ xs →
                   ρ (algODʳ D xs) (algODᶜ E (λ xs' → f (xs , xs')))

algODᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) {X : I → Set ℓ}
        → Algᶜˢ D X → ConODs (Σ[ i ∈ I ] X i × ⊤) fst D (List.map (algConB ℓ) cbs)
algODᶜˢ []       f = []
algODᶜˢ (D ∷ Ds) f = algODᶜ D (f ∘ inl) ∷ ∺ algODᶜˢ Ds (f ∘ inr)

module _ (ℓ : Level) where

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

  algOD-pfp-lemma :
      (ℓⁱ ℓᵃ : Level) (cbs : ConBs)
    → maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ maxMap (hasRec? (ℓᵃ ⊔ ℓⁱ)) cbs ⊔
      hasCon? ℓⁱ cbs ⊔ ℓᵃ ⊔ ℓⁱ ≡ ℓᵃ ⊔ ℓⁱ
    → maxMap max-π (List.map (algConB ℓ) cbs) ⊔
      maxMap max-σ (List.map (algConB ℓ) cbs) ⊔
      maxMap (hasRec? (ℓᵃ ⊔ ℓⁱ ⊔ ℓ)) (List.map (algConB ℓ) cbs) ⊔
      hasCon? (ℓⁱ ⊔ ℓ) (List.map (algConB ℓ) cbs) ⊔ ℓᵃ ⊔ ℓⁱ ⊔ ℓ ≡ ℓᵃ ⊔ ℓⁱ ⊔ ℓ
  algOD-pfp-lemma ℓⁱ ℓᵃ cbs pfp' =
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

algODᵈ : ∀ (D : DataD) {ℓf} {X : Carriers D ℓf} → Algs D X → DataOD D
algODᵈ D {ℓf} {X} f = record
  { #levels = DataD.#levels D
  ; level   = λ ℓs → ℓs
  ; applyL  = λ ℓs → let Dᵖ = DataD.applyL D ℓs in record
      { alevel = PDataD.alevel Dᵖ
      ; level-pre-fixed-point = algOD-pfp-lemma
          (ℓf ℓs) (PDataD.ilevel Dᵖ) (PDataD.dlevel Dᵖ) (PDataD.struct Dᵖ)
          (PDataD.level-pre-fixed-point Dᵖ)
      ; Param  = PDataD.Param Dᵖ
      ; param  = id
      ; Index  = λ ps → PDataD.Index Dᵖ ps ++ λ is → X ℓs ps is ∷ λ _ → []
      ; index  = λ _ → fst
      ; applyP = λ ps → algODᶜˢ (PDataD.applyP Dᵖ ps) f } }

algOD : ∀ (D : DataD) {ℓf} → Algebrasᵗ D ℓf → DataOD D
algOD D alg = algODᵈ D (Algebra.apply (alg $$ _ $$ _))

rememberʳ :
    {I : Set ℓⁱ} (D : RecD I rb) {X : I → Set ℓˣ}
    {N : I → Set ℓ} (fold : ∀ {i} → N i → X i) {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
  → (ns : ⟦ D ⟧ʳ N) → Allʳ D (λ i' n → N' (i' , fold n , tt)) ns
  → ⟦ ⌊ algODʳ D (fmapʳ D fold ns) ⌋ʳ ⟧ʳ N'
rememberʳ (ι i  ) fold ns n'  = n'
rememberʳ (π A D) fold ns all = λ a → rememberʳ (D a) fold (ns a) (all a)

rememberᶜ :
    {I : Set ℓⁱ} (D : ConD I cb) {X : I → Set ℓˣ} (f : Algᶜ D X)
    {N : I → Set ℓ} (fold : ∀ {i} → N i → X i) {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
  → ∀ {i} (ns : ⟦ D ⟧ᶜ N i) → Allᶜ D (λ i' n → N' (i' , fold n , tt)) ns ℓ''
  → ⟦ ⌊ algODᶜ D f ⌋ᶜ ⟧ᶜ N' (i , f (fmapᶜ D fold ns) , tt)
rememberᶜ (ι i  ) f fold refl        all = refl
rememberᶜ (σ A D) f fold (a  , ns )  all = a , rememberᶜ (D a) (curry f a) fold ns all
rememberᶜ (ρ D E) f fold (ns , ns') (all , all') =
  fmapʳ D fold ns , rememberʳ D fold ns all , rememberᶜ E (curry f _) fold ns' all'

rememberᶜˢ :
    {I : Set ℓⁱ} (D : ConDs I cbs) {X : I → Set ℓˣ} (f : Algᶜˢ D X)
    {N : I → Set ℓ} (fold : ∀ {i} → N i → X i) {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
  → ∀ {i} (ns : ⟦ D ⟧ᶜˢ N i) → Allᶜˢ D (λ i' n → N' (i' , fold n , tt)) ns ℓ''
  → ⟦ ⌊ algODᶜˢ D f ⌋ᶜˢ ⟧ᶜˢ N' (i , f (fmapᶜˢ D fold ns) , tt)
rememberᶜˢ (D ∷ Ds) f fold (inl ns) all = inl (rememberᶜ  D  (f ∘ inl) fold ns all)
rememberᶜˢ (D ∷ Ds) f fold (inr ns) all = inr (rememberᶜˢ Ds (f ∘ inr) fold ns all)

remember-alg :
  ∀ {D N} (C : DataC D N) {ℓf : DataD.Levels D → Level}
    (alg : Algebrasᵗ D ℓf) (fold : FoldsTᵗ C alg) → AlgebrasCᵗ C alg fold
  → ∀ {N'} (C' : DataC ⌊ algOD D alg ⌋ᵈ N') → IndAlgebrasᵗ C _
remember-alg {D} {N} C alg fold foldC {N'} C' $$ ℓs $$ ps = record
  { Carrier = λ is n → N' ℓs ps (is , (fold $$ ℓs $$ ps) n , tt)
  ; apply = let Dᶜˢ = PDataD.applyP (DataD.applyL D ℓs) ps in λ ns all →
      DataC.toN C' (subst (λ x → ⟦ ⌊ algOD D alg ⌋ᵈ ⟧ᵈ (N' ℓs ps) (_ , x , tt))
                          (sym (foldC ns))
                          (rememberᶜˢ Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps))
                             (fold $$ ℓs $$ ps) ns all)) }
