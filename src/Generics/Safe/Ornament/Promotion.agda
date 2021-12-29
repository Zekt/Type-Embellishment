{-# OPTIONS --safe #-}

module Generics.Safe.Ornament.Promotion where

open import Prelude
open import Generics.Safe.Telescope; open ∀ℓ; open ∀ᵗ
open import Generics.Safe.Description
open import Generics.Safe.Ornament
open import Generics.Safe.Algebra
open import Generics.Safe.Recursion

orn-alg : ∀ {D E N} (O : DataO D E) → DataC E N
        → ∀ℓ _ λ ℓs → ∀ᵗ false _ λ ps → Algebraᵈ D ℓs ps _
orn-alg {N = N} O C $$ ℓs $$ ps = record
  { Carrier = λ is → let Oᵖ = DataO.applyL O ℓs
                     in  N (DataO.level  O  ℓs   )
                           (PDataO.param Oᵖ ps   )
                           (PDataO.index Oᵖ ps is)
  ; apply = DataC.toN C ∘ eraseᵈ O }
