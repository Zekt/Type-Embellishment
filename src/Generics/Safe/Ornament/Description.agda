{-# OPTIONS --safe #-}

module Generics.Safe.Ornament.Description where

open import Prelude
open import Generics.Safe.Telescope
open import Generics.Safe.Description
open import Generics.Safe.Ornament

private variable
  A : Set ℓ
  n : ℕ
  rb  rb'  : RecB
  cb  cb'  : ConB
  cbs cbs' : ConBs

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
    alevel   : Level
    {plevel} : Level
    {ilevel} : Level
    {struct} : ConBs
  dlevel : Level
  dlevel = alevel ⊔ ilevel
  flevel : Level → Level
  flevel ℓ = maxMap max-π struct ⊔ maxMap max-σ struct ⊔
             maxMap (hasRec? ℓ) struct ⊔ hasCon? ilevel struct
  field
    level-pre-fixed-point : flevel dlevel ⊑ dlevel
    Param  : MTel plevel
    param  : ⟦ Param ⟧ᵐᵗ → ⟦ PDataD.Param E ⟧ᵐᵗ
    Index  : ⟦ Param ⟧ᵐᵗ → MTel ilevel
    index  : (ps : ⟦ Param ⟧ᵐᵗ) → ⟦ Index ps ⟧ᵐᵗ → ⟦ PDataD.Index E (param ps) ⟧ᵐᵗ
    applyP : (ps : ⟦ Param ⟧ᵐᵗ)
           → ConODs ⟦ Index ps ⟧ᵐᵗ (index ps) (PDataD.applyP E (param ps)) struct

record DataOD (E : DataD) : Setω where
  field
    #levels : ℕ
  Levels : Set
  Levels = Level ^ #levels
  field
    level  : Levels → DataD.Levels E
    applyL : (ℓs : Levels) → PDataOD (DataD.applyL E (level ℓs))

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
  { alevel = PDataOD.alevel OD
  ; level-pre-fixed-point = PDataOD.level-pre-fixed-point OD
  ; Param  = PDataOD.Param OD
  ; Index  = PDataOD.Index OD
  ; applyP = λ ps → ⌊ PDataOD.applyP OD ps ⌋ᶜˢ }

⌈_⌉ᵖᵈ : ∀ {E} (OD : PDataOD E) → PDataO ⌊ OD ⌋ᵖᵈ E
⌈ OD ⌉ᵖᵈ = record
  { param  = PDataOD.param OD
  ; index  = PDataOD.index OD
  ; applyP = λ ps → ⌈ PDataOD.applyP OD ps ⌉ᶜˢ }

⌊_⌋ᵈ : ∀ {E} → DataOD E → DataD
⌊ OD ⌋ᵈ = record
  { #levels = DataOD.#levels OD
  ; applyL = λ ℓs → ⌊ DataOD.applyL OD ℓs ⌋ᵖᵈ }

⌈_⌉ᵈ : ∀ {E} (OD : DataOD E) → DataO ⌊ OD ⌋ᵈ E
⌈ OD ⌉ᵈ = record
  { level  = DataOD.level OD
  ; applyL = λ ℓs → ⌈ DataOD.applyL OD ℓs ⌉ᵖᵈ }
