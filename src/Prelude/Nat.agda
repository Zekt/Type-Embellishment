{-# OPTIONS --safe #-}

module Prelude.Nat where

open import Prelude.Level
open import Prelude.Equality

open import Agda.Builtin.Nat public
  using (zero; suc; _+_; _*_; _==_)
  renaming (Nat to ℕ; _<_ to _<ᵇ_; _-_ to _∸_)
