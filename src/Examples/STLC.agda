{-# OPTIONS --safe --with-K #-}

module Examples.STLC where

open import Prelude hiding (idFun)

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
UntypedTermT = genDataT UntypedTermD Λ
UntypedTermC = genDataC UntypedTermD UntypedTermT

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
TypedTermT = genDataT TypedTermD _⊢_
TypedTermC = genDataC TypedTermD TypedTermT

TypedTermO : DataO TypedTermD UntypedTermD
TypedTermO = record
  { level  = λ _ → tt
  ; applyL = λ _ → record
      { param  = λ _ → tt
      ; index  = λ _ _ → tt
      ; applyP = λ _ → (Δ[ Γ ] Δ[ τ ] Δ[ i ] ∇ (toℕ _ _ i) ι)  -- [FIXME]
                   ∷ ∺ (Δ[ Γ ] Δ[ τ ] Δ[ τ' ] ρ ι (ρ ι ι))
                   ∷ ∺ (Δ[ τ ] Δ[ Γ ] Δ[ τ' ] ρ ι ι) ∷ ∺ [] } }

TypingOD : DataOD TypedTermD
TypingOD = AlgOD (forget TypedTermC UntypedTermC TypedTermO)

infix 3 _⊢_⦂_

-- unquoteDecl data Typing constructor var' app' lam' = defineByDataD ⌊ TypingOD ⌋ᵈ Typing (var' ∷ app' ∷ lam' ∷ [])
data _⊢_⦂_ : List Ty → Λ → Ty → Set₀ where

  var : ∀ {Γ τ} (i : ListAny Ty (_≡_ τ) Γ)
      → ------------------------------
        Γ ⊢ var (toℕ Ty (_≡_ τ) i) ⦂ τ

  app : ∀ {Γ τ τ' t} → Γ ⊢ t ⦂ τ ⇒ τ'
      → ∀ {u}        → Γ ⊢ u ⦂ τ
      → -----------------------------
        Γ ⊢ app t u ⦂ τ'
  lam : ∀ {τ Γ τ' t} → τ ∷ Γ ⊢ t ⦂ τ'
      → -----------------------------
        Γ ⊢ lam t ⦂ τ ⇒ τ'

TypingT : DataT ⌊ TypingOD ⌋ᵈ
TypingT tt tt ((x , x₁ , tt) , x₂ , tt) = x ⊢ x₂ ⦂ x₁

TypingC = genDataC ⌊ TypingOD ⌋ᵈ TypingT

fromTypingP : FoldP
fromTypingP = forget TypingC TypedTermC ⌈ TypingOD ⌉ᵈ

-- unquoteDecl fromTyping = defineFold fromTypingP fromTyping
fromTyping : ∀ {Γ τ t} (z : Γ ⊢ t ⦂ τ) → Γ ⊢ τ
fromTyping (var i  ) = var i
fromTyping (app d e) = app (fromTyping d) (fromTyping e)
fromTyping (lam d  ) = lam (fromTyping d)

fromTypingT = genFoldT fromTypingP fromTyping
fromTypingC = genFoldC fromTypingP fromTypingT

toTyping : 

-- [TODO] Γ ⊢ τ ≅ Σ[ t ∈ Λ ] Γ ⊢ t ⦂ τ
