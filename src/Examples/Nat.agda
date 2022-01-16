{-# OPTIONS --safe --without-K #-}

module Examples.Nat where

open import Prelude
open import Generics.Telescope
open import Generics.Description

-- [ＭＥＴＡ]
NatD : DataD
NatD = record
  { #levels = 0
  ; applyL  = λ _ → record
      { alevel = 0ℓ
      ; Param  = []
      ; Index  = λ _ → []
      ; applyP = λ _ → ι tt ∷ ρ (ι tt) (ι tt) ∷ [] } }
