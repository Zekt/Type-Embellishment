{-# OPTIONS --without-K #-}

open import Prelude

module Generics.Telescope where

infixr 5 _∷_

_^_ : Set → ℕ → Set
A ^ zero  = ⊤
A ^ suc n = A × (A ^ n)

{-# NO_UNIVERSE_CHECK #-}
data Tel : Level → Set

⟦_⟧ᵗ : Tel ℓ → Set ℓ

data Tel where
    []   : Tel lzero
    _∷_  : (A : Set ℓ) (T : A → Tel ℓ') → Tel (ℓ ⊔ ℓ')
    _++_ : (T : Tel ℓ) (U : ⟦ T ⟧ᵗ → Tel ℓ') → Tel (ℓ ⊔ ℓ')

⟦ []     ⟧ᵗ = ⊤
⟦ A ∷  T ⟧ᵗ = Σ A λ a → ⟦ T a ⟧ᵗ
⟦ T ++ U ⟧ᵗ = Σ ⟦ T ⟧ᵗ λ t → ⟦ U t ⟧ᵗ

∷-syntaxᵗ : (A : Set ℓ) (T : A → Tel ℓ') → Tel (ℓ ⊔ ℓ')
∷-syntaxᵗ = _∷_

syntax ∷-syntaxᵗ A (λ x → T) = [ x ∶ A ] T

Curriedᵗ : (visible : Bool) (T : Tel ℓ) (X : ⟦ T ⟧ᵗ → Set ℓ') → Set (ℓ ⊔ ℓ')
Curriedᵗ _     []       X = X tt
Curriedᵗ false (A ∷  T) X = {a : A} → Curriedᵗ false (T a) (curry X a)
Curriedᵗ true  (A ∷  T) X = (a : A) → Curriedᵗ true  (T a) (curry X a)
Curriedᵗ v     (T ++ U) X = Curriedᵗ v T λ t → Curriedᵗ v (U t) λ u → X (t , u)

curryᵗ : (T : Tel ℓ) (X : ⟦ T ⟧ᵗ → Set ℓ') {visible : Bool}
        → ((t : ⟦ T ⟧ᵗ) → X t) → Curriedᵗ visible T X
curryᵗ []       X         f = f tt
curryᵗ (A ∷  T) X {false} f =       curryᵗ (T _) (curry X _) (curry f _)
curryᵗ (A ∷  T) X {true } f = λ a → curryᵗ (T a) (curry X a) (curry f a)
curryᵗ (T ++ U) X         f = curryᵗ T _ λ t → curryᵗ (U t) _ λ u → f (t , u)

uncurryᵗ : (T : Tel ℓ) (X : ⟦ T ⟧ᵗ → Set ℓ') {visible : Bool}
          → Curriedᵗ visible T X → (t : ⟦ T ⟧ᵗ) → X t
uncurryᵗ []       X         f tt      = f
uncurryᵗ (A ∷  T) X {false} f (a , t) = uncurryᵗ (T a) (curry X a)  f    t
uncurryᵗ (A ∷  T) X {true } f (a , t) = uncurryᵗ (T a) (curry X a) (f a) t
uncurryᵗ (T ++ U) X         f (t , u) = uncurryᵗ (U t) _ (uncurryᵗ T _ f t) u

record ∀ᵗ (visible : Bool) {ℓ ℓ'} (T : Tel ℓ) (X : ⟦ T ⟧ᵗ → Set ℓ') : Set (ℓ ⊔ ℓ') where
  field _$$_ : (t : ⟦ T ⟧ᵗ) → X t
  infixl -100 _$$_

record ∀ℓ (n : ℕ) {ℓf : Level ^ n → Level} (X : (ℓs : Level ^ n) → Set (ℓf ℓs)) : Setω where
  field _$$_ : (ℓs : Level ^ n) → X ℓs
  infixl -100 _$$_

record ∀ℓω (n : ℕ) (X : Level ^ n → Setω) : Setω where
  field _$$_ : (ℓs : Level ^ n) → X ℓs
  infixl -100 _$$_
