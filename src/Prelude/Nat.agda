{-# OPTIONS --safe #-}

module Prelude.Nat where

open import Agda.Builtin.Unit
open import Prelude.Empty
open import Prelude.Bool

open import Agda.Builtin.Nat as ℕ public
  using (zero; suc; _+_; _*_)
  renaming (Nat to ℕ; _<_ to _<ᵇ_; _-_ to _∸_)


_≤?_ : ℕ → ℕ → Bool
zero  ≤? _     = true
suc m ≤? zero  = false
suc m ≤? suc n = m ≤? n

_<?_ : ℕ → ℕ → Bool
m <? n = suc m ≤? n

infix 4 _≤_ _<_

_≤_ : ℕ → ℕ → Set
m ≤ n = T (m ≤? n)

_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n
