{-# OPTIONS --safe #-}

module Generics.Prelude where

open import Agda.Primitive        public
open import Agda.Builtin.Sigma    public
open import Agda.Builtin.Equality public

record Unit {ℓ} : Set ℓ where
  constructor tt

data Empty {ℓ} : Set ℓ where

data Sum {ℓ₀ ℓ₁} (A : Set ℓ₀) (B : Set ℓ₁) : Set (ℓ₀ ⊔ ℓ₁) where
  inl : A → Sum A B
  inr : B → Sum A B

id : ∀ {ℓ} {A : Set ℓ} → A → A
id a = a

curry : ∀ {ℓᵃ ℓᵇ ℓᶜ} {A : Set ℓᵃ} {B : A → Set ℓᵇ} {C : Σ A B → Set ℓᶜ}
      → ((p : Σ A B) → C p) → (a : A) (b : B a) → C (a , b)
curry f a b = f (a , b)

uncurry : ∀ {ℓᵃ ℓᵇ ℓᶜ} {A : Set ℓᵃ} {B : A → Set ℓᵇ} {C : Σ A B → Set ℓᶜ}
        → ((a : A) (b : B a) → C (a , b)) → (p : Σ A B) → C p
uncurry f (a , b) = f a b

sym : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq

cong : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y : A} → x ≡ y → P x → P y
subst P refl p = p