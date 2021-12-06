{-# OPTIONS --safe #-}

module Generics.Safe.Ornament.Description where

open import Prelude
open import Generics.Safe.Description
open import Generics.Safe.Ornament

private variable
  A : Set ℓ
  rb rb' : RecB
  cb cb' : ConB
  cbs cbs' : ConBs

module _ (I : Set ℓⁱ) {J : Set ℓʲ} (e : I → J) where

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
    ∅   : ConODs ∅ []
    _◁_ : {E : ConD J cb} {Es : ConDs J cbs}
          (OD : ConOD E cb') (ODs : ConODs (E ◁ Es) cbs')
        → ConODs (E ◁ Es) (cb' ∷ cbs')
    ◂_  : {E : ConD J cb} {Es : ConDs J cbs}
          (ODs : ConODs Es cbs') → ConODs (E ◁ Es) cbs'

  infixr 4 _◁_
  infix  4 ◂_

record DataOD (E : DataD) : Setω where
  field
    {plevel} : Level
    {ilevel} : Level
    {struct} : ConBs
  flevel : Level → Level
  flevel ℓ = maxMap max-π struct ⊔ maxMap max-σ struct ⊔
             maxMap (hasRec? ℓ) struct ⊔ hasCon? ilevel struct
  field
    level : Level
    level-pre-fixed-point : flevel level ⊔ level ≡ level
    Param : Tel plevel
    param : ⟦ Param ⟧ᵗ → ⟦ DataD.Param E ⟧ᵗ
    Index : ⟦ Param ⟧ᵗ → Tel ilevel
    index : (p : ⟦ Param ⟧ᵗ) → ⟦ Index p ⟧ᵗ → ⟦ DataD.Index E (param p) ⟧ᵗ
    OrnDesc : (p : ⟦ Param ⟧ᵗ)
            → ConODs ⟦ Index p ⟧ᵗ (index p) (DataD.Desc E (param p)) struct

record UPDataOD (E : UPDataD) : Setω where
  field
    #levels : ℕ
  Levels : Set
  Levels = Level ^ #levels
  field
    levels  : Levels → UPDataD.Levels E
    OrnDesc : (ℓs : Levels) → DataOD (UPDataD.Desc E (levels ℓs))

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
  ⌊ ∅        ⌋ᶜˢ = ∅
  ⌊ OD ◁ ODs ⌋ᶜˢ = ⌊ OD ⌋ᶜ ◁ ⌊ ODs ⌋ᶜˢ
  ⌊    ◂ ODs ⌋ᶜˢ = ⌊ ODs ⌋ᶜˢ

  ⌈_⌉ᶜˢ : {Es : ConDs J cbs} (ODs : ConODs I e Es cbs') → ConOs e ⌊ ODs ⌋ᶜˢ Es
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
