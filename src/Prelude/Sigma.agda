{-# OPTIONS --safe #-}
module Prelude.Sigma where

open import Agda.Builtin.Sigma public
  hiding (module Σ)
module Σ = Agda.Builtin.Sigma.Σ

private variable
  A B C : Set _

infix 2 Σ-syntax

Σ-syntax : ∀ {a b}
  → (A : Set a) → (A → Set b) → Set _
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

infixr 2 _×_

_×_ : ∀ {a b}
  → (A : Set a) (B : Set b) → Set _
A × B = Σ[ _ ∈ A ] B

bimap : ∀ {ℓ} {P : A → Set ℓ} {ℓ′} {Q : B → Set ℓ′} →
      (f : A → B) → (∀ {x} → P x → Q (f x)) →
      Σ A P → Σ B Q
bimap f g (x , y) = (f x , g y)
