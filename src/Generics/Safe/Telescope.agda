{-# OPTIONS --safe --without-K #-}

module Generics.Safe.Telescope where

open import Prelude

infixr 5 _∷_
infixr 4 _++_

mutual

  data Tel : Level → Setω where
    []   : Tel lzero
    _∷_  : (A : Set ℓ) (T : A → Tel ℓ') → Tel (ℓ ⊔ ℓ')
    _++_ : (T : Tel ℓ) (U : ⟦ T ⟧ᵗ → Tel ℓ') → Tel (ℓ ⊔ ℓ')

  ⟦_⟧ᵗ : Tel ℓ → Set ℓ
  ⟦ []     ⟧ᵗ = ⊤
  ⟦ A ∷  T ⟧ᵗ = Σ A λ a → ⟦ T a ⟧ᵗ
  ⟦ T ++ U ⟧ᵗ = Σ ⟦ T ⟧ᵗ λ t → ⟦ U t ⟧ᵗ

∷-syntaxᵗ : (A : Set ℓ) (T : A → Tel ℓ') → Tel (ℓ ⊔ ℓ')
∷-syntaxᵗ = _∷_

syntax ∷-syntaxᵗ A (λ x → T) = [ x ∶ A ] T

Curriedᵗ : (T : Tel ℓ) (X : ⟦ T ⟧ᵗ → Set ℓ') → Set (ℓ ⊔ ℓ')
Curriedᵗ []       X = X tt
Curriedᵗ (A ∷  T) X = (a : A) → Curriedᵗ (T a) (curry X a)
Curriedᵗ (T ++ U) X = Curriedᵗ T λ t → Curriedᵗ (U t) λ u → X (t , u)

curryᵗ : (T : Tel ℓ) (X : ⟦ T ⟧ᵗ → Set ℓ')
       → ((t : ⟦ T ⟧ᵗ) → X t) → Curriedᵗ T X
curryᵗ []       X f = f tt
curryᵗ (A ∷  T) X f = λ a → curryᵗ (T a) (curry X a) (curry f a)
curryᵗ (T ++ U) X f = curryᵗ T _ λ t → curryᵗ (U t) _ λ u → f (t , u)

uncurryᵗ : (T : Tel ℓ) (X : ⟦ T ⟧ᵗ → Set ℓ')
         → Curriedᵗ T X → (t : ⟦ T ⟧ᵗ) → X t
uncurryᵗ []       X f tt      = f
uncurryᵗ (A ∷  T) X f (a , t) = uncurryᵗ (T a) (curry X a) (f a) t
uncurryᵗ (T ++ U) X f (t , u) = uncurryᵗ (U t) _ (uncurryᵗ T _ f t) u

_^_ : Set → ℕ → Set
A ^ zero  = ⊤
A ^ suc n = A × (A ^ n)
