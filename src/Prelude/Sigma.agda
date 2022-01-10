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

infixr 4 _,ω_

record Σω {a} (A : Set a) (B : A → Setω) : Setω where
  constructor _,ω_
  field
    fst : A
    snd : B fst

open Σω public

infix 2 Σω-syntax

Σω-syntax : ∀ {a} (A : Set a) → (A → Setω) → Setω
Σω-syntax = Σω

syntax Σω-syntax A (λ x → B) = Σω[ x ∈ A ] B

infixr 4 _,ωω_

record Σωω (A : Setω) (B : A → Setω) : Setω where
  constructor _,ωω_
  field
    fst : A
    snd : B fst

open Σωω public

infix 2 Σωω-syntax

Σωω-syntax : (A : Setω) → (A → Setω) → Setω
Σωω-syntax = Σωω

syntax Σωω-syntax A (λ x → B) = Σωω[ x ∈ A ] B

infixr 4 _,ℓ_

record Σℓ {ℓf : Level → Level} (B : ∀ ℓ → Set (ℓf ℓ)) : Setω where
  constructor _,ℓ_
  field
    fst : Level
    snd : B fst

open Σℓ public

infix 2 Σℓ-syntax

Σℓ-syntax : {ℓf : Level → Level} → (∀ ℓ → Set (ℓf ℓ)) → Setω
Σℓ-syntax = Σℓ

syntax Σℓ-syntax (λ ℓ → B) = Σℓ[ ℓ ] B
