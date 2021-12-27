{-# OPTIONS --without-K --safe #-}
module Prelude.Sigma where

open import Prelude.Level

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

<_,_> : {B : A → Set ℓ} {C : {x : A} → B x → Set ℓ'}
        (f : (x : A) → B x) → ((x : A) → C (f x)) →
        ((x : A) → Σ (B x) C)
< f , g > x = (f x , g x)

bimap : ∀ {ℓ} {P : A → Set ℓ} {ℓ′} {Q : B → Set ℓ′} →
      (f : A → B) → (∀ {x} → P x → Q (f x)) →
      Σ A P → Σ B Q
bimap f g (x , y) = (f x , g y)

curry : ∀ {ℓᵃ} {A : Set ℓᵃ} {ℓᵇ} {B : A → Set ℓᵇ} {ℓᶜ} {C : Σ A B → Set ℓᶜ} →
        ((p : Σ A B) → C p) →
        ((x : A) → (y : B x) → C (x , y))
curry f x y = f (x , y)

uncurry : ∀ {ℓᵃ} {A : Set ℓᵃ} {ℓᵇ} {B : A → Set ℓᵇ} {ℓᶜ} {C : Σ A B → Set ℓᶜ} →
          ((x : A) → (y : B x) → C (x , y)) →
          ((p : Σ A B) → C p)
uncurry f (x , y) = f x y
