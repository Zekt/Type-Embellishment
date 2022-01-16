{-# OPTIONS --safe --with-K #-}

module Examples.List where

open import Prelude
open import Generics.Telescope
open import Generics.Description
open import Generics.Ornament.Description
open import Examples.Nat

ListOD : DataOD NatD
ListOD = record
  { #levels = 1
  ; applyL  = λ (ℓ , _) → record
      { alevel = ℓ
      ; Param  = [ A ∶ Set ℓ ] []
      ; Index  = λ _ → []
      ; applyP = λ (A , _) → ι tt ∷ ∺ (Δ A λ _ → ρ (ι tt) (ι tt)) ∷ ∺ [] } }
