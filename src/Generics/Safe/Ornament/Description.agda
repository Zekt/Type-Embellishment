{-# OPTIONS --safe #-}

module Generics.Safe.Ornament.Description where

open import Prelude
open import Generics.Safe.Description
open import Generics.Safe.Ornament

private variable
  A : Set ℓ
  rb  rb'  : RecB
  cb  cb'  : ConB
  cbs cbs' : ConBs

mutual

  data TelOD : Tel ℓ → Level → Setω where
    ε : {U : Tel ℓ} → TelOD U ℓ
    ▷ : {U : Tel ℓ''} (OD : TelOD U ℓ)
      → (⟦ ⌊ OD ⌋ᵗ ⟧ᵗ → Set ℓ') → TelOD U (ℓ ⊔ ℓ')
    κ : {A : Set ℓ} {U : A → Tel ℓ''}
      → (OD : ∀ a → TelOD (U a) ℓ') → TelOD (A ∷ U) (ℓ ⊔ ℓ')
    Δ : (A : Set ℓ) {U : Tel ℓ''}
      → (OD : A → TelOD U ℓ') → TelOD U (ℓ ⊔ ℓ')
    ∇ : (a : A) {U : A → Tel ℓ''}
      → (OD : TelOD (U a) ℓ') → TelOD (A ∷ U) ℓ'

  ⌊_⌋ᵗ : {U : Tel ℓ'} → TelOD U ℓ → Tel ℓ
  ⌊ ε {U = U} ⌋ᵗ = U
  ⌊ ▷ OD A    ⌋ᵗ = snocᵗ ⌊ OD ⌋ᵗ A
  ⌊ κ   OD    ⌋ᵗ = _ ∷ λ a → ⌊ OD a ⌋ᵗ
  ⌊ Δ A OD    ⌋ᵗ = A ∷ λ a → ⌊ OD a ⌋ᵗ
  ⌊ ∇ a OD    ⌋ᵗ = ⌊ OD ⌋ᵗ

⌈_⌉ᵗ : {U : Tel ℓ'} (OD : TelOD U ℓ) → TelO ⌊ OD ⌋ᵗ U
⌈ ε      ⌉ᵗ = ε
⌈ ▷ OD A ⌉ᵗ = ▷ ⌈ OD ⌉ᵗ
⌈ κ   OD ⌉ᵗ = κ λ a → ⌈ OD a ⌉ᵗ
⌈ Δ A OD ⌉ᵗ = Δ λ a → ⌈ OD a ⌉ᵗ
⌈ ∇ a OD ⌉ᵗ = ∇ a ⌈ OD ⌉ᵗ

module _ (I : Set ℓⁱ) {J : Set ℓʲ} (e : I → J) where

  infixr 5 _∷_
  infix  5 ∺_

  data RecOD : RecD J rb → Setω where
    ι : ∀ i {j} (eq : e i ≡ j) → RecOD (ι j)
    π : {E : A → RecD J rb} (OD : (a : A) → RecOD (E a)) → RecOD (π A E)

  data ConOD : ConD J cb → ConB → Setω where
    ι : ∀ i {j} (eq : e i ≡ j) → ConOD (ι j) []
    σ : {A : Set ℓ} {E : A → ConD J cb}
        (OD : (a : A) → ConOD (E a) cb') → ConOD (σ A E) (inl ℓ ∷ cb')
    Δ : (A : Set ℓ) {E : ConD J cb}
        (OD : (a : A) → ConOD E cb') → ConOD E (inl ℓ ∷ cb')
    ∇ : {E : A → ConD J cb} (a : A) (OD : ConOD (E a) cb') → ConOD (σ A E) cb'
    ρ : {S : RecD J rb} {E : ConD J cb}
        (OD : RecOD S) (OD' : ConOD E cb') → ConOD (ρ S E) (inr rb ∷ cb')

  data ConODs : ConDs J cbs → ConBs → Setω where
    []  : ConODs [] []
    _∷_ : {E : ConD J cb} {Es : ConDs J cbs}
          (OD : ConOD E cb') (ODs : ConODs (E ∷ Es) cbs')
        → ConODs (E ∷ Es) (cb' ∷ cbs')
    ∺_  : {E : ConD J cb} {Es : ConDs J cbs}
          (ODs : ConODs Es cbs') → ConODs (E ∷ Es) cbs'

record PDataOD (E : PDataD) : Setω where
  field
    {plevel} : Level
    {ilevel} : Level
    {struct} : ConBs
  flevel : Level → Level
  flevel ℓ = maxMap max-π struct ⊔ maxMap max-σ struct ⊔
             maxMap (hasRec? ℓ) struct ⊔ hasCon? ilevel struct
  field
    dlevel  : Level
    level-pre-fixed-point : let ℓ = dlevel ⊔ ilevel in flevel ℓ ⊔ ℓ ≡ ℓ
    ParamOD : TelOD (PDataD.Param E) plevel
    IndexOD : (p : ⟦ ⌊ ParamOD ⌋ᵗ ⟧ᵗ)
            → TelOD (PDataD.Index E (eraseᵗ ⌈ ParamOD ⌉ᵗ p)) ilevel
    applyP  : (p : ⟦ ⌊ ParamOD ⌋ᵗ ⟧ᵗ)
            → ConODs ⟦ ⌊ IndexOD p ⌋ᵗ ⟧ᵗ (eraseᵗ ⌈ IndexOD p ⌉ᵗ)
                (PDataD.applyP E (eraseᵗ ⌈ ParamOD ⌉ᵗ p)) struct

record DataOD (E : DataD) : Setω where
  field
    #levels : ℕ
  Levels : Set
  Levels = Level ^ #levels
  field
    levels : Levels → DataD.Levels E
    applyL : (ℓs : Levels) → PDataOD (DataD.applyL E (levels ℓs))

module _ {I : Set ℓⁱ} {J : Set ℓʲ} {e : I → J} where

  ⌊_⌋ʳ : {E : RecD J rb} → RecOD I e E → RecD I rb
  ⌊ ι i eq ⌋ʳ = ι i
  ⌊ π OD   ⌋ʳ = π _ λ a → ⌊ OD a ⌋ʳ

  ⌈_⌉ʳ : {E : RecD J rb} (OD : RecOD I e E) → RecO e ⌊ OD ⌋ʳ E
  ⌈ ι i eq ⌉ʳ = ι eq
  ⌈ π OD   ⌉ʳ = π λ a → ⌈ OD a ⌉ʳ

  ⌊_⌋ᶜ : {E : ConD J cb} → ConOD I e E cb' → ConD I cb'
  ⌊ ι i eq   ⌋ᶜ = ι i
  ⌊ ρ OD OD' ⌋ᶜ = ρ ⌊ OD ⌋ʳ ⌊ OD' ⌋ᶜ
  ⌊ σ    OD  ⌋ᶜ = σ _ λ a → ⌊ OD a ⌋ᶜ
  ⌊ Δ A  OD  ⌋ᶜ = σ A λ a → ⌊ OD a ⌋ᶜ
  ⌊ ∇ a  OD  ⌋ᶜ = ⌊ OD ⌋ᶜ

  ⌈_⌉ᶜ : {E : ConD J cb} (OD : ConOD I e E cb') → ConO e ⌊ OD ⌋ᶜ E
  ⌈ ι i eq   ⌉ᶜ = ι eq
  ⌈ ρ OD OD' ⌉ᶜ = ρ ⌈ OD ⌉ʳ ⌈ OD' ⌉ᶜ
  ⌈ σ    OD  ⌉ᶜ = σ λ a → ⌈ OD a ⌉ᶜ
  ⌈ Δ A  OD  ⌉ᶜ = Δ λ a → ⌈ OD a ⌉ᶜ
  ⌈ ∇ a  OD  ⌉ᶜ = ∇ a ⌈ OD ⌉ᶜ

  ⌊_⌋ᶜˢ : {Es : ConDs J cbs} → ConODs I e Es cbs' → ConDs I cbs'
  ⌊ []       ⌋ᶜˢ = []
  ⌊ OD ∷ ODs ⌋ᶜˢ = ⌊ OD ⌋ᶜ ∷ ⌊ ODs ⌋ᶜˢ
  ⌊    ∺ ODs ⌋ᶜˢ = ⌊ ODs ⌋ᶜˢ

  ⌈_⌉ᶜˢ : {Es : ConDs J cbs} (ODs : ConODs I e Es cbs') → ConOs e ⌊ ODs ⌋ᶜˢ Es
  ⌈ []       ⌉ᶜˢ = []
  ⌈ OD ∷ ODs ⌉ᶜˢ = ⌈ OD ⌉ᶜ ∷ ⌈ ODs ⌉ᶜˢ
  ⌈    ∺ ODs ⌉ᶜˢ =         ∺ ⌈ ODs ⌉ᶜˢ

⌊_⌋ᵖᵈ : ∀ {E} → PDataOD E → PDataD
⌊ OD ⌋ᵖᵈ = record
  { dlevel  = PDataOD.dlevel OD
  ; level-pre-fixed-point = PDataOD.level-pre-fixed-point OD
  ; Param  = ⌊ PDataOD.ParamOD OD ⌋ᵗ
  ; Index  = λ p → ⌊ PDataOD.IndexOD OD p ⌋ᵗ
  ; applyP = λ p → ⌊ PDataOD.applyP OD p ⌋ᶜˢ
  }

⌈_⌉ᵖᵈ : ∀ {E} (OD : PDataOD E) → PDataO ⌊ OD ⌋ᵖᵈ E
⌈ OD ⌉ᵖᵈ = record
  { ParamO = ⌈ PDataOD.ParamOD OD ⌉ᵗ
  ; IndexO = λ p → ⌈ PDataOD.IndexOD OD p ⌉ᵗ
  ; applyP = λ p → ⌈ PDataOD.applyP OD p ⌉ᶜˢ
  }

⌊_⌋ᵈ : ∀ {E} → DataOD E → DataD
⌊ OD ⌋ᵈ = record
  { #levels = DataOD.#levels OD
  ; applyL = λ ℓs → ⌊ DataOD.applyL OD ℓs ⌋ᵖᵈ }

⌈_⌉ᵈ : ∀ {E} (OD : DataOD E) → DataO ⌊ OD ⌋ᵈ E
⌈ OD ⌉ᵈ = record
  { levels = DataOD.levels OD
  ; applyL = λ ℓs → ⌈ DataOD.applyL OD ℓs ⌉ᵖᵈ }

module ODFunctor {I : Set ℓⁱ} {J : Set ℓʲ} {e : I → J}
  {K : Set ℓᵏ} (f : I → K) (e' : K → J) (coh : ∀ i → e' (f i) ≡ e i) where

  imapʳ : {D : RecD J rb} → RecOD I e D → RecOD K e' D
  imapʳ (ι i eq) = ι (f i) (trans (coh i) eq)
  imapʳ (π OD  ) = π λ a → imapʳ (OD a)

  imapᶜ : {D : ConD J cb} → ConOD I e D cb' → ConOD K e' D cb'
  imapᶜ (ι i eq  ) = ι (f i) (trans (coh i) eq)
  imapᶜ (σ    OD ) = σ λ a → imapᶜ (OD a)
  imapᶜ (Δ A  OD ) = Δ A λ a → imapᶜ (OD a)
  imapᶜ (∇ a  OD ) = ∇ a (imapᶜ OD)
  imapᶜ (ρ OD OD') = ρ (imapʳ OD) (imapᶜ OD')

  imapᶜˢ : {D : ConDs J cbs} → ConODs I e D cbs' → ConODs K e' D cbs'
  imapᶜˢ []         = []
  imapᶜˢ (OD ∷ ODs) = imapᶜ OD ∷ imapᶜˢ ODs
  imapᶜˢ (   ∺ ODs) =          ∺ imapᶜˢ ODs
