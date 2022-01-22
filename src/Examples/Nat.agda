{-# OPTIONS --safe --without-K #-}

module Examples.Nat where

open import Prelude

open import Generics.Description
open import Generics.Recursion
open import Generics.Reflection

open import Generics.RecursionScheme

--------
-- Connecting with the existing ℕ datatype

NatD = genDataD ℕ
NatC = genDataC NatD (genDataT NatD ℕ)
-- [FAIL] This checks, but foldℕC below wouldn’t
-- NatC = let NatD = genDataD ℕ
--        in  genDataC NatD (genDataT NatD ℕ)

--------
-- Fold operator and fusion theorem

-- unquoteDecl foldℕ = defineFold (fold-operator NatC) foldℕ
foldℕ : {X : Set ℓ} → X → (X → X) → ℕ → X
foldℕ z s  zero   = z
foldℕ z s (suc n) = s (foldℕ z s n)

foldℕC = genFoldC (fold-operator NatC) (genFoldT (fold-operator NatC) foldℕ)

foldℕ-fusion :
    {X : Set ℓ} {Y : Set ℓ'} (h : X → Y) (z : X) (s : X → X) (z' : Y) (s' : Y → Y)
  → h z ≡ z' → ((x : X) (y : Y) → y ≡ h x → h (s x) ≡ s' y)
  → (n : ℕ) → h (foldℕ z s n) ≡ foldℕ z' s' n
foldℕ-fusion h z s z' s' hz hs  zero   = trans hz refl
foldℕ-fusion h z s z' s' hz hs (suc n) =
  trans (hs (foldℕ z s n) (foldℕ z' s' n) (sym (foldℕ-fusion h z s z' s' hz hs n))) refl

foldℕ-fusionC = genIndC (fold-fusion NatC foldℕC)
               (genIndT (fold-fusion NatC foldℕC) foldℕ-fusion)

--------
-- Induction operator

-- unquoteDecl indℕ = defineInd (ind-operator NatC) indℕ
indℕ : {P : ℕ → Set ℓ} → P 0 → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
indℕ z s  zero   = z
indℕ z s (suc n) = s n (indℕ z s n)

indℕT = genIndT (ind-operator NatC) indℕ
indℕC = genIndC (ind-operator NatC) indℕT
-- [FAIL] unsolved constraints
-- indℕC = genIndC (ind-operator NatC) (genIndT (ind-operator NatC) indℕ)
-- unquoteDecl foldℕ-fusion = defineInd (fold-fusion NatC foldℕC) foldℕ-fusion
