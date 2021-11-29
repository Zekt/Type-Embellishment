{-# OPTIONS --safe #-}

module Prelude.Level where

open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit renaming (⊤ to Unit)

_^_ : Set → Nat → Set
A ^ zero  = Unit
A ^ suc n = Σ A λ _ → A ^ n
