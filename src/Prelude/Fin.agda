{-# OPTIONS --safe --without-K #-}

module Prelude.Fin where

open import Agda.Builtin.Unit
open import Prelude.Empty
open import Prelude.Nat

private variable
  m n : ℕ

data Fin : ℕ → Set where
  zero : Fin (suc n)
  suc  : (i : Fin n) → Fin (suc n)

toℕ : Fin n → ℕ
toℕ zero    = 0
toℕ (suc i) = suc (toℕ i)

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero    = zero
fromℕ (suc n) = suc (fromℕ n)
