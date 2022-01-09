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

++-syntaxᵗ : (A : Tel ℓ) (T : ⟦ A ⟧ᵗ → Tel ℓ') → Tel (ℓ ⊔ ℓ')
++-syntaxᵗ = _++_

syntax ++-syntaxᵗ T (λ x → U) = [[ x ∶ T ]] U

Curriedᵗ : (visible : Bool) (T : Tel ℓ) (X : ⟦ T ⟧ᵗ → Set ℓ') → Set (ℓ ⊔ ℓ')
Curriedᵗ _     []       X = X tt
Curriedᵗ false (A ∷  T) X = {a : A} → Curriedᵗ false (T a) (curry X a)
Curriedᵗ true  (A ∷  T) X = (a : A) → Curriedᵗ true  (T a) (curry X a)
Curriedᵗ v     (T ++ U) X = Curriedᵗ v T λ t → Curriedᵗ v (U t) λ u → X (t , u)

curryᵗ : {T : Tel ℓ} {X : ⟦ T ⟧ᵗ → Set ℓ'} {visible : Bool}
       → ((t : ⟦ T ⟧ᵗ) → X t) → Curriedᵗ visible T X
curryᵗ {T = []    }             f = f tt
curryᵗ {T = A ∷  T} {_} {false} f =       curryᵗ {T = T _} (curry f _)
curryᵗ {T = A ∷  T} {_} {true } f = λ a → curryᵗ {T = T a} (curry f a)
curryᵗ {T = T ++ U}             f = curryᵗ {T = T} λ t → curryᵗ {T = U t} λ u → f (t , u)

uncurryᵗ : {T : Tel ℓ} {X : ⟦ T ⟧ᵗ → Set ℓ'} {visible : Bool}
         → Curriedᵗ visible T X → (t : ⟦ T ⟧ᵗ) → X t
uncurryᵗ {T = []    }             f tt      = f
uncurryᵗ {T = A ∷  T} {_} {false} f (a , t) = uncurryᵗ {T = T a}  f    t
uncurryᵗ {T = A ∷  T} {_} {true } f (a , t) = uncurryᵗ {T = T a} (f a) t
uncurryᵗ {T = T ++ U}             f (t , u) = uncurryᵗ {T = U t} (uncurryᵗ {T = T} f t) u

_^_ : Set → ℕ → Set
A ^ zero  = ⊤
A ^ suc n = A × (A ^ n)
