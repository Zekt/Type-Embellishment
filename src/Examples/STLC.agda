{-# OPTIONS --safe --with-K #-}

module Examples.STLC where

open import Prelude
open import Generics.Telescope
open import Generics.Description
open import Generics.Ornament
open import Generics.RecursionScheme
open import Generics.SimpleContainer.Any
open import Metalib.Datatype
open import Metalib.Connection
open import Metalib.Recursion
open import Utils.Reflection hiding (Term)

infixr 5 _⇒_
infix  3 _⊢_

data Ty : Set where
  base : Ty
  _⇒_  : Ty → Ty → Ty

data Term : Set where
  var : ℕ → Term
  app : Term → Term → Term
  lam : Term → Term

-- [META]
_∋_ : {A : Set} → List A → A → Set
xs ∋ x = Any (x ≡_) xs

variable
  τ τ' : Ty
  Γ    : List Ty

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

TermD = genDataD _⊢_
TermC = genDataC TermD _⊢_

unquoteDecl foldTerm = defineFold (fold-operator TermC) foldTerm
