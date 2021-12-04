{-# OPTIONS --safe #-}

module Generics.Safe.Ornament.Description where

open import Prelude
open import Generics.Safe.Description
open import Generics.Safe.Ornament

private
  variable
    cρ cρ' : ℕ
    cρs cρs' : List ℕ
    A : Set ℓᵃ

module _ (I : Set ℓⁱ) {J : Set ℓʲ} (e : I → J) where

  data RecOD : RecD J ℓʳ → Setω where
    ι : ∀ i {j} (eq : e i ≡ j) → RecOD (ι j)
    π : {E : A → RecD J ℓʳ} (OD : (a : A) → RecOD (E a)) → RecOD (π A E)

  data ConOD : ConD J ℓᵃ cρ → Level → Setω where
    ι : ∀ i {j} (eq : e i ≡ j) → ConOD (ι j) lzero
    ρ : {S : RecD J ℓʳ} {E : ConD J ℓ cρ}
        (OD : RecOD S) (OD' : ConOD E ℓ') → ConOD (ρ S E) (ℓʳ ⊔ ℓ')
    σ : {A : Set ℓᵃ} {E : A → ConD J ℓ cρ}
        (OD : (a : A) → ConOD (E a) ℓ') → ConOD (σ A E) (ℓᵃ ⊔ ℓ')
    Δ : (A : Set ℓᵃ) {E : ConD J ℓ cρ}
        (OD : (a : A) → ConOD E ℓ') → ConOD E (ℓᵃ ⊔ ℓ')
    ∇ : {E : A → ConD J ℓ cρ} (a : A) (OD : ConOD (E a) ℓ') → ConOD (σ A E) ℓ'

  data ConODs : ConDs J ℓᵃ cρs → Level → List ℕ → Setω where
    ∅   : ConODs ∅ lzero []
    _◁_ : {E : ConD J ℓ₀ cρ} {Es : ConDs J ℓ₁ cρs}
          (OD : ConOD E ℓ₂) (ODs : ConODs (E ◁ Es) ℓ₃ cρs')
        → ConODs (E ◁ Es) (ℓ₂ ⊔ ℓ₃) (cρ ∷ cρs')
    ◂_  : {E : ConD J ℓ₀ cρ} {Es : ConDs J ℓ₁ cρs}
          (ODs : ConODs Es ℓ₂ cρs') → ConODs (E ◁ Es) ℓ₂ cρs'

  infixr 4 _◁_
  infix  4 ◂_

record DataOD (E : DataD) : Setω where
  field
    {plevel} : Level
    {ilevel} : Level
    {alevel} : Level
    {recCounts} : List ℕ
  flevel : Level → Level
  flevel ℓ = alevel ⊔ lconds recCounts ℓ ⊔ lcond (length recCounts) ilevel
  field
    level : Level
    level-pre-fixed-point : flevel level ⊔ level ≡ level
    Param : Tel plevel
    param : ⟦ Param ⟧ᵗ → ⟦ DataD.Param E ⟧ᵗ
    Index : ⟦ Param ⟧ᵗ → Tel ilevel
    index : (p : ⟦ Param ⟧ᵗ) → ⟦ Index p ⟧ᵗ → ⟦ DataD.Index E (param p) ⟧ᵗ
    OrnDesc : (p : ⟦ Param ⟧ᵗ)
            → ConODs ⟦ Index p ⟧ᵗ (index p) (DataD.Desc E (param p)) alevel recCounts

record UPDataOD (E : UPDataD) : Setω where
  field
    #levels : ℕ
  Levels : Set
  Levels = Level ^ #levels
  field
    levels  : Levels → UPDataD.Levels E
    OrnDesc : (ℓs : Levels) → DataOD (UPDataD.Desc E (levels ℓs))

module _ {ℓⁱ ℓʲ} {I : Set ℓⁱ} {J : Set ℓʲ} {e : I → J} where

  ⌊_⌋ʳ : {E : RecD J ℓʳ} → RecOD I e E → RecD I ℓʳ
  ⌊ ι i eq ⌋ʳ = ι i
  ⌊ π OD   ⌋ʳ = π _ λ a → ⌊ OD a ⌋ʳ

  ⌈_⌉ʳ : {E : RecD J ℓʳ} (OD : RecOD I e E) → RecO e ⌊ OD ⌋ʳ E
  ⌈ ι i eq ⌉ʳ = ι eq
  ⌈ π OD   ⌉ʳ = π λ a → ⌈ OD a ⌉ʳ

  ⌊_⌋ᶜ : {E : ConD J ℓ cρ} → ConOD I e E ℓ' → ConD I ℓ' cρ
  ⌊ ι i eq   ⌋ᶜ = ι i
  ⌊ ρ OD OD' ⌋ᶜ = ρ ⌊ OD ⌋ʳ ⌊ OD' ⌋ᶜ
  ⌊ σ    OD  ⌋ᶜ = σ _ λ a → ⌊ OD a ⌋ᶜ
  ⌊ Δ A  OD  ⌋ᶜ = σ A λ a → ⌊ OD a ⌋ᶜ
  ⌊ ∇ a  OD  ⌋ᶜ = ⌊ OD ⌋ᶜ

  ⌈_⌉ᶜ : {E : ConD J ℓ cρ} (OD : ConOD I e E ℓ') → ConO e ⌊ OD ⌋ᶜ E
  ⌈ ι i eq   ⌉ᶜ = ι eq
  ⌈ ρ OD OD' ⌉ᶜ = ρ ⌈ OD ⌉ʳ ⌈ OD' ⌉ᶜ
  ⌈ σ    OD  ⌉ᶜ = σ λ a → ⌈ OD a ⌉ᶜ
  ⌈ Δ A  OD  ⌉ᶜ = Δ λ a → ⌈ OD a ⌉ᶜ
  ⌈ ∇ a  OD  ⌉ᶜ = ∇ a ⌈ OD ⌉ᶜ

  ⌊_⌋ᶜˢ : {Es : ConDs J ℓ cρs} → ConODs I e Es ℓ' cρs' → ConDs I ℓ' cρs'
  ⌊ ∅        ⌋ᶜˢ = ∅
  ⌊ OD ◁ ODs ⌋ᶜˢ = ⌊ OD ⌋ᶜ ◁ ⌊ ODs ⌋ᶜˢ
  ⌊    ◂ ODs ⌋ᶜˢ = ⌊ ODs ⌋ᶜˢ

  ⌈_⌉ᶜˢ : {Es : ConDs J ℓ cρs} (ODs : ConODs I e Es ℓ' cρs') → ConOs e ⌊ ODs ⌋ᶜˢ Es
  ⌈ ∅        ⌉ᶜˢ = ∅
  ⌈ OD ◁ ODs ⌉ᶜˢ = ⌈ OD ⌉ᶜ ◁ ⌈ ODs ⌉ᶜˢ
  ⌈    ◂ ODs ⌉ᶜˢ =         ◂ ⌈ ODs ⌉ᶜˢ

⌊_⌋ᵈ : ∀ {E} → DataOD E → DataD
⌊ OD ⌋ᵈ = record
  { level = DataOD.level OD
  ; level-pre-fixed-point = DataOD.level-pre-fixed-point OD
  ; Param = DataOD.Param OD
  ; Index = DataOD.Index OD
  ; Desc  = λ p → ⌊ DataOD.OrnDesc OD p ⌋ᶜˢ
  }

⌈_⌉ᵈ : ∀ {E} (OD : DataOD E) → DataO ⌊ OD ⌋ᵈ E
⌈ OD ⌉ᵈ = record
  { param = DataOD.param OD
  ; index = DataOD.index OD
  ; Orn   = λ p → ⌈ DataOD.OrnDesc OD p ⌉ᶜˢ
  }

⌊_⌋ᵘᵖᵈ : ∀ {E} → UPDataOD E → UPDataD
⌊ OD ⌋ᵘᵖᵈ = record
  { #levels = UPDataOD.#levels OD
  ; Desc    = λ ℓs → ⌊ UPDataOD.OrnDesc OD ℓs ⌋ᵈ }

⌈_⌉ᵘᵖᵈ : ∀ {E} (OD : UPDataOD E) → UPDataO ⌊ OD ⌋ᵘᵖᵈ E
⌈ OD ⌉ᵘᵖᵈ = record
  { levels = UPDataOD.levels OD
  ; Orn    = λ ℓs → ⌈ UPDataOD.OrnDesc OD ℓs ⌉ᵈ }
