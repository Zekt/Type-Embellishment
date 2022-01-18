{-# OPTIONS --safe --with-K #-}

module Examples.STLC where

open import Prelude

open import Generics.Telescope
open import Generics.Description
open import Generics.Recursion
open import Generics.Reflection

open import Generics.Ornament
open import Generics.Ornament.Description
open import Generics.Ornament.Algebraic

open import Examples.Nat
open import Examples.List

--------
-- Untyped λ-calculus

data Λ : Set where
  var : ℕ → Λ
  app : Λ → Λ → Λ
  lam : Λ → Λ

UntypedTermD = genDataD Λ
UntypedTermC = genDataC UntypedTermD Λ  -- [FIXME]

--------
-- Simply typed λ-calculus

infixr 5 _⇒_

data Ty : Set where
  base : Ty
  _⇒_  : Ty → Ty → Ty

variable
  τ τ' : Ty
  Γ    : List Ty

infix 3 _⊢_

data _⊢_ : List Ty → Ty → Set where

  var : Γ ∋ τ
      → -----
        Γ ⊢ τ

  app : Γ ⊢ τ ⇒ τ'
      → Γ ⊢ τ
        ----------
      → Γ ⊢ τ'

  lam : τ ∷ Γ ⊢ τ'
      → ----------
        Γ ⊢ τ ⇒ τ'

TypedTermD = genDataD _⊢_
TypedTermC = genDataC TypedTermD _⊢_

TypedTermO : DataO TypedTermD UntypedTermD
TypedTermO = record
  { level  = λ _ → tt
  ; applyL = λ _ → record
      { param  = λ _ → tt
      ; index  = λ _ _ → tt
      ; applyP = λ _ → (Δ[ Γ ] Δ[ τ ] Δ[ i ] ∇ (toℕ  _ _ i) ι)  -- [FIXME]
                   ∷ ∺ (Δ[ Γ ] Δ[ τ ] Δ[ τ' ] ρ ι (ρ ι ι))
                   ∷ ∺ (Δ[ τ ] Δ[ Γ ] Δ[ τ' ] ρ ι ι) ∷ ∺ [] } }

TypingOD : DataOD TypedTermD
TypingOD = AlgOD (forget TypedTermC UntypedTermC TypedTermO)

-- [TODO] Γ ⊢ τ ≅ Σ[ t ∈ Λ ] ⊢ t ⦂ τ
