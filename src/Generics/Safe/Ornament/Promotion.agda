{-# OPTIONS --safe #-}

module Generics.Safe.Ornament.Promotion where

open import Prelude
open import Generics.Safe.Telescope
open import Generics.Safe.Description
open import Generics.Safe.Algebra
open import Generics.Safe.Recursion
open import Generics.Safe.Ornament
open import Generics.Safe.Ornament.Description
open import Generics.Safe.Ornament.Algebraic

PromOD : ∀ {D M} → DataC D M → ∀ {E N} → DataC E N → DataO D E → DataOD D
PromOD C C' O = AlgOD (forget C C' O)

PromD : ∀ {D M} → DataC D M → ∀ {E N} → DataC E N → DataO D E → DataD
PromD C C' O = ⌊ PromOD C C' O ⌋ᵈ
