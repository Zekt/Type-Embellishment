{-# OPTIONS --without-K #-}

open import Prelude hiding (_++_)

module Generics.Telescope where

infixr 5 _∷_

{-# NO_UNIVERSE_CHECK #-}
data Tel : Level → Set where
  []  : Tel lzero
  _∷_ : (A : Set ℓ) (T : A → Tel ℓ') → Tel (ℓ ⊔ ℓ')

-- de Bruijn's notation

∷-syntax : (A : Set ℓ) (T : A → Tel ℓ') → Tel (ℓ ⊔ ℓ')
∷-syntax = _∷_

syntax ∷-syntax A (λ x → T) = [ x ∶ A ] T

⟦_⟧ᵗ : Tel ℓ → Set ℓ
⟦ []    ⟧ᵗ = ⊤
⟦ A ∷ T ⟧ᵗ = Σ A λ a → ⟦ T a ⟧ᵗ

_++_ : (tel : Tel ℓ) → (⟦ tel ⟧ᵗ → Tel ℓ') → Tel (ℓ ⊔ ℓ')
_++_ []      U = U tt
_++_ (A ∷ T) U = A ∷ λ x → (T x) ++ λ ⟦Tx⟧ → U (x , ⟦Tx⟧)

Curried : ∀ {ℓ ℓ'} → (T : Tel ℓ) → (⟦ T ⟧ᵗ → Set ℓ') → Set (ℓ ⊔ ℓ')
Curried []      X = X tt
Curried (A ∷ T) X = (a : A) → Curried (T a) λ t → X (a , t)

curryⁿ : (T : Tel ℓ) (X : ⟦ T ⟧ᵗ → Set ℓ') → ((t : ⟦ T ⟧ᵗ) → X t) → Curried T X
curryⁿ []      X f = f tt
curryⁿ (A ∷ T) X f = λ a → curryⁿ (T a) (λ t → X (a , t)) (λ t → f (a , t))

uncurryⁿ : (T : Tel ℓ) (X : ⟦ T ⟧ᵗ → Set ℓ′) → Curried T X → (t : ⟦ T ⟧ᵗ) → X t
uncurryⁿ []      X f tt      = f
uncurryⁿ (A ∷ T) X f (x , t) = uncurryⁿ (T x) (λ t → X (x , t)) (f x) t

_^_ : Set → ℕ → Set
A ^ zero  = ⊤
A ^ suc n = A × (A ^ n)
