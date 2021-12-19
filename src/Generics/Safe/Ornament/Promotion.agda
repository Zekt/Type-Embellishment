{-# OPTIONS --safe #-}

module Generics.Safe.Ornament.Promotion where

open import Prelude
open import Generics.Safe.Description
open import Generics.Safe.Ornament
open import Generics.Safe.Algebra
open import Generics.Safe.Recursion

orn-alg : ∀ {D E N} (O : DataO D E) → DataC E N → ∀ ℓs ps → Algebraᵈ D ℓs ps _
orn-alg {N = N} O C ℓs ps = record
  { Carrier = λ is → let Oᵖ = DataO.applyL O ℓs
                     in  N (erase# (DataO.LevelO  O    ) ℓs)
                           (eraseᵗ (PDataO.ParamO Oᵖ   ) ps)
                           (eraseᵗ (PDataO.IndexO Oᵖ ps) is)
  ; apply = DataC.toN C ∘ eraseᵈ O }
