{-# OPTIONS --safe #-}
module Prelude.Fin where

open import Agda.Builtin.Nat using (zero; suc; _+_; _*_)
  renaming (Nat to ℕ)

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → (i : Fin n) → Fin (suc n)
