{-# OPTIONS --safe --without-K --show-implicit #-}

module Examples.Nat where

open import Prelude

open import Generics.Telescope
open import Generics.Description
open import Generics.Reflection
open import Generics.Recursion

open import Generics.RecursionScheme

NatD = genDataD ℕ

NatT = genDataT NatD ℕ

NatC = genDataC NatD ℕ  -- [FIXME]

-- [TODO] print function definitions directly

unquoteDecl foldℕ = defineFold (fold-operator NatC) foldℕ  -- [FIXME]
foldℕ-wrapper = genFoldGT (fold-operator NatC) foldℕ 

-- [TODO] fold fusion

-- unquoteDecl indℕ = defineInd (ind-operator NatC) indℕ
indℕ : {ℓ : Level} {P : ℕ → Set ℓ} →
  P 0 → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
indℕ base ind zero    = base
indℕ base ind (suc n) = ind n (indℕ base ind n)

indℕ-wrapper = genIndGT (ind-operator NatC) indℕ
