{-# OPTIONS --safe #-}

module Generics.Ornament.Description where

open import Generics.Prelude
open import Generics.Description
open import Generics.Ornament

data RecOD {ℓ} {I J : Set ℓ} (e : I → J) : RecD J → Set (lsuc ℓ) where
  ι : ∀ (i : I) {j} (eq : e i ≡ j) → RecOD e (ι j)
  π : ∀ {A E} (OD : (a : A) → RecOD e (E a)) → RecOD e (π A E)

⌊_⌋ʳ : ∀ {ℓ} {I J : Set ℓ} {e : I → J} {E} → RecOD e E → RecD I
⌊ ι i eq ⌋ʳ = ι i
⌊ π OD   ⌋ʳ = π _ λ a → ⌊ OD a ⌋ʳ

⌈_⌉ʳ : ∀ {ℓ} {I J : Set ℓ} {e : I → J} {E} (OD : RecOD e E) → RecO e ⌊ OD ⌋ʳ E
⌈ ι i eq ⌉ʳ = ι eq
⌈ π OD   ⌉ʳ = π λ a → ⌈ OD a ⌉ʳ

data ConOD {ℓ} {I J : Set ℓ} (e : I → J) : ConD J → Set (lsuc ℓ) where
  ι : ∀ (i : I) {j} (eq : e i ≡ j) → ConOD e (ι j)
  ρ : ∀ {S E} (OD : RecOD e S) (OD' : ConOD e E) → ConOD e (ρ S E)
  σ : ∀ {A E}           (OD : (a : A) → ConOD e (E a)) → ConOD e (σ A E)
  Δ : ∀ {A : Set ℓ} {E} (OD : (a : A) → ConOD e  E   ) → ConOD e      E
  ∇ : ∀ {A E}  (a : A)  (OD :           ConOD e (E a)) → ConOD e (σ A E)

⌊_⌋ᶜ : ∀ {ℓ} {I J : Set ℓ} {e : I → J} {E} → ConOD e E → ConD I
⌊ ι i eq   ⌋ᶜ = ι i
⌊ ρ OD OD' ⌋ᶜ = ρ ⌊ OD ⌋ʳ ⌊ OD' ⌋ᶜ
⌊ σ    OD  ⌋ᶜ = σ _ λ a → ⌊ OD a ⌋ᶜ
⌊ Δ    OD  ⌋ᶜ = σ _ λ a → ⌊ OD a ⌋ᶜ
⌊ ∇ a  OD  ⌋ᶜ = ⌊ OD ⌋ᶜ

⌈_⌉ᶜ : ∀ {ℓ} {I J : Set ℓ} {e : I → J} {E} (OD : ConOD e E) → ConO e ⌊ OD ⌋ᶜ E
⌈ ι i eq   ⌉ᶜ = ι eq
⌈ ρ OD OD' ⌉ᶜ = ρ ⌈ OD ⌉ʳ ⌈ OD' ⌉ᶜ
⌈ σ    OD  ⌉ᶜ = σ λ a → ⌈ OD a ⌉ᶜ
⌈ Δ    OD  ⌉ᶜ = Δ λ a → ⌈ OD a ⌉ᶜ
⌈ ∇ a  OD  ⌉ᶜ = ∇ a ⌈ OD ⌉ᶜ

data ConODs {ℓ} {I J : Set ℓ} (e : I → J) : ConDs J → Set (lsuc ℓ) where
  ∅   : ConODs e ∅
  _◁_ : ∀ {E Es} (OD : ConOD e E) (ODs : ConODs e (E ◁ Es)) → ConODs e (E ◁ Es)
  ◂_  : ∀ {E Es}                  (ODs : ConODs e      Es ) → ConODs e (E ◁ Es)

infixr 4 _◁_
infix  4 ◂_

⌊_⌋ᶜˢ : ∀ {ℓ} {I J : Set ℓ} {e : I → J} {E} → ConODs e E → ConDs I
⌊ ∅        ⌋ᶜˢ = ∅
⌊ OD ◁ ODs ⌋ᶜˢ = ⌊ OD ⌋ᶜ ◁ ⌊ ODs ⌋ᶜˢ
⌊    ◂ ODs ⌋ᶜˢ = ⌊ ODs ⌋ᶜˢ

⌈_⌉ᶜˢ : ∀ {ℓ} {I J : Set ℓ} {e : I → J} {E} (OD : ConODs e E) → ConOs e ⌊ OD ⌋ᶜˢ E
⌈ ∅        ⌉ᶜˢ = ∅
⌈ OD ◁ ODs ⌉ᶜˢ = ⌈ OD ⌉ᶜ ◁ ⌈ ODs ⌉ᶜˢ
⌈    ◂ ODs ⌉ᶜˢ =         ◂ ⌈ ODs ⌉ᶜˢ

record SetOD {ℓᵖ ℓⁱ} (E : SetD {ℓᵖ} {ℓⁱ}) : Set (lsuc (ℓᵖ ⊔ ℓⁱ)) where
  field
    Param : Tel ℓᵖ
    param : ⟦ Param ⟧ᵗ → ⟦ SetD.Param E ⟧ᵗ
    Index : ⟦ Param ⟧ᵗ → Tel ℓⁱ
    index : (p : ⟦ Param ⟧ᵗ) → ⟦ Index p ⟧ᵗ → ⟦ SetD.Index E (param p) ⟧ᵗ
    Orn   : (p : ⟦ Param ⟧ᵗ) → ConODs (index p) (SetD.Desc E (param p))

⌊_⌋ˢ : ∀ {ℓᵖ ℓⁱ} {E : SetD {ℓᵖ} {ℓⁱ}} → SetOD E → SetD
⌊ OD ⌋ˢ = record
  { Param = SetOD.Param OD
  ; Index = SetOD.Index OD
  ; Desc  = λ p → ⌊ SetOD.Orn OD p ⌋ᶜˢ }

⌈_⌉ˢ : ∀ {ℓᵖ} {ℓⁱ} {E} (OD : SetOD {ℓᵖ} {ℓⁱ} E) → SetO ⌊ OD ⌋ˢ E
⌈ OD ⌉ˢ = record
  { param = SetOD.param OD
  ; index = SetOD.index OD
  ; Orn   = λ p → ⌈ SetOD.Orn OD p ⌉ᶜˢ }