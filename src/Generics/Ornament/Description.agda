{-# OPTIONS --safe #-}

module Generics.Ornament.Description where

open import Generics.Prelude
open import Generics.Description
open import Generics.Ornament

private
  variable
    ℓ ℓ' ℓ'' ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓⁱ ℓʲ ℓᵃ : Level
    ℓf ℓg ℓh ℓk : Level → Level
    I : Set ℓⁱ
    J : Set ℓʲ
    A : Set ℓᵃ

data RecOD (e : I → J) : RecD J ℓf → Setω where
  ι : ∀ i {j} (eq : e i ≡ j) → RecOD e (ι j)
  π : {E : A → RecD J ℓf} (OD : (a : A) → RecOD e (E a)) → RecOD e (π A E)

⌊_⌋ʳ : {e : I → J} {E : RecD J ℓf} → RecOD e E → RecD I ℓf
⌊ ι i eq ⌋ʳ = ι i
⌊ π OD   ⌋ʳ = π _ λ a → ⌊ OD a ⌋ʳ

⌈_⌉ʳ : {e : I → J} {E : RecD J ℓf} (OD : RecOD e E) → RecO e ⌊ OD ⌋ʳ E
⌈ ι i eq ⌉ʳ = ι eq
⌈ π OD   ⌉ʳ = π λ a → ⌈ OD a ⌉ʳ

data ConOD {I : Set ℓⁱ} {J : Set ℓʲ}
            (e : I → J) : ConD J ℓf → (Level → Level) → Setω where
  ι : ∀ i {j} (eq : e i ≡ j) → ConOD e (ι j) (λ _ → ℓⁱ)
  ρ : {S : RecD J ℓf} {E : ConD J ℓg}
      (OD : RecOD e S) (OD' : ConOD e E ℓh) → ConOD e (ρ S E) (λ ℓ → ℓf ℓ ⊔ ℓh ℓ)
  σ : {A : Set ℓᵃ} {E : A → ConD J ℓf}
      (OD : (a : A) → ConOD e (E a) ℓg) → ConOD e (σ A E) (λ ℓ → ℓᵃ ⊔ ℓg ℓ)
  Δ : (A : Set ℓᵃ) {E : ConD J ℓf}
      (OD : (a : A) → ConOD e E ℓg) → ConOD e E (λ ℓ → ℓᵃ ⊔ ℓg ℓ)
  ∇ : {E : A → ConD J ℓf} (a : A) (OD : ConOD e (E a) ℓg) → ConOD e (σ A E) ℓg

⌊_⌋ᶜ : {e : I → J} {E : ConD J ℓf} → ConOD e E ℓg → ConD I ℓg
⌊ ι i eq   ⌋ᶜ = ι i
⌊ ρ OD OD' ⌋ᶜ = ρ ⌊ OD ⌋ʳ ⌊ OD' ⌋ᶜ
⌊ σ    OD  ⌋ᶜ = σ _ λ a → ⌊ OD a ⌋ᶜ
⌊ Δ A  OD  ⌋ᶜ = σ A λ a → ⌊ OD a ⌋ᶜ
⌊ ∇ a  OD  ⌋ᶜ = ⌊ OD ⌋ᶜ

⌈_⌉ᶜ : {e : I → J} {E : ConD J ℓf} (OD : ConOD e E ℓg) → ConO e ⌊ OD ⌋ᶜ E
⌈ ι i eq   ⌉ᶜ = ι eq
⌈ ρ OD OD' ⌉ᶜ = ρ ⌈ OD ⌉ʳ ⌈ OD' ⌉ᶜ
⌈ σ    OD  ⌉ᶜ = σ λ a → ⌈ OD a ⌉ᶜ
⌈ Δ A  OD  ⌉ᶜ = Δ λ a → ⌈ OD a ⌉ᶜ
⌈ ∇ a  OD  ⌉ᶜ = ∇ a ⌈ OD ⌉ᶜ

data ConODs (e : I → J) : ConDs J ℓf → (Level → Level) → Setω where
  ∅   : ConODs e ∅ (λ _ → lzero)
  _◁_ : {E : ConD J ℓf} {Es : ConDs J ℓg}
        (OD : ConOD e E ℓh) (ODs : ConODs e (E ◁ Es) ℓk)
      → ConODs e (E ◁ Es) (λ ℓ → ℓh ℓ ⊔ ℓk ℓ)
  ◂_  : {E : ConD J ℓf} {Es : ConDs J ℓg}
        (ODs : ConODs e Es ℓh) → ConODs e (E ◁ Es) ℓh

infixr 4 _◁_
infix  4 ◂_

⌊_⌋ᶜˢ : {e : I → J} {Es : ConDs J ℓf} → ConODs e Es ℓg → ConDs I ℓg
⌊ ∅        ⌋ᶜˢ = ∅
⌊ OD ◁ ODs ⌋ᶜˢ = ⌊ OD ⌋ᶜ ◁ ⌊ ODs ⌋ᶜˢ
⌊    ◂ ODs ⌋ᶜˢ = ⌊ ODs ⌋ᶜˢ

⌈_⌉ᶜˢ : {e : I → J} {Es : ConDs J ℓf} (ODs : ConODs e Es ℓg) → ConOs e ⌊ ODs ⌋ᶜˢ Es
⌈ ∅        ⌉ᶜˢ = ∅
⌈ OD ◁ ODs ⌉ᶜˢ = ⌈ OD ⌉ᶜ ◁ ⌈ ODs ⌉ᶜˢ
⌈    ◂ ODs ⌉ᶜˢ =         ◂ ⌈ ODs ⌉ᶜˢ

record LMDataOD (E : LMDataD) : Setω where
  field
    {plevel} : Level
    {ilevel} : Level
    {flevel} : Level → Level
    level : Level
    level-fixed-point : flevel level ≡ level
    Param : Tel plevel
    param : ⟦ Param ⟧ᵗ → ⟦ LMDataD.Param E ⟧ᵗ
    Index : ⟦ Param ⟧ᵗ → Tel ilevel
    index : (p : ⟦ Param ⟧ᵗ) → ⟦ Index p ⟧ᵗ → ⟦ LMDataD.Index E (param p) ⟧ᵗ
    OrnDesc : (p : ⟦ Param ⟧ᵗ) → ConODs (index p) (LMDataD.Desc E (param p)) flevel

⌊_⌋ᵈᵐ : ∀ {E} → LMDataOD E → LMDataD
⌊ OD ⌋ᵈᵐ = record
  { level = LMDataOD.level OD
  ; level-fixed-point = LMDataOD.level-fixed-point OD
  ; Param = LMDataOD.Param OD
  ; Index = LMDataOD.Index OD
  ; Desc  = λ p → ⌊ LMDataOD.OrnDesc OD p ⌋ᶜˢ
  }

⌈_⌉ᵈᵐ : ∀ {E} (OD : LMDataOD E) → LMDataO ⌊ OD ⌋ᵈᵐ E
⌈ OD ⌉ᵈᵐ = record
  { param = LMDataOD.param OD
  ; index = LMDataOD.index OD
  ; Orn   = λ p → ⌈ LMDataOD.OrnDesc OD p ⌉ᶜˢ
  }

record DataOD (E : DataD) : Setω where
  constructor dataOD
  field
    #level : Nat
  Levels : Set
  Levels = Level ^ #level
  field
    levels : Levels → DataD.Levels E
    OrnDesc : (ℓs : Levels) → LMDataOD (DataD.Desc E (levels ℓs))

⌊_⌋ᵈ : ∀ {E} → DataOD E → DataD
⌊ OD ⌋ᵈ = dataD (DataOD.#level OD) λ ℓs → ⌊ DataOD.OrnDesc OD ℓs ⌋ᵈᵐ

⌈_⌉ᵈ : ∀ {E} (OD : DataOD E) → DataO ⌊ OD ⌋ᵈ E
⌈ OD ⌉ᵈ = dataO (DataOD.levels OD) λ ℓs → ⌈ DataOD.OrnDesc OD ℓs ⌉ᵈᵐ