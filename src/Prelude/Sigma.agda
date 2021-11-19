module Prelude.Sigma where

open import Agda.Builtin.Sigma public
  hiding (module Σ)
module Σ = Agda.Builtin.Sigma.Σ

infix 2 Σ-syntax

Σ-syntax : ∀ {a b}
  → (A : Set a) → (A → Set b) → Set _
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

infixr 2 _×_

_×_ : ∀ {a b}
  → (A : Set a) (B : Set b) → Set _
A × B = Σ[ _ ∈ A ] B
