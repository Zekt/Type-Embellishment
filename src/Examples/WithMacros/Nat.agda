{-# OPTIONS --safe --without-K #-}

module Examples.WithMacros.Nat where

open import Prelude

open import Generics.Description
open import Generics.Recursion
open import Generics.Reflection

open import Generics.RecursionScheme

--------
-- Connecting with the existing ℕ datatype

instance
  NatC : Named (quote ℕ) _
  unNamed NatC = genDataC NatD (genDataT NatD ℕ)
    where NatD = genDataD ℕ

--------
-- Fold operator and fusion theorem

private
  foldℕP : FoldP
  foldℕP = fold-operator (quote ℕ)

unquoteDecl foldℕ = defineFold foldℕP foldℕ
-- foldℕ : {X : Set ℓ} → X → (X → X) → ℕ → X
-- foldℕ z s  zero   = z
-- foldℕ z s (suc n) = s (foldℕ z s n)

instance foldℕC = genFoldC foldℕP foldℕ

private
  foldℕ-fusionP : IndP
  foldℕ-fusionP = fold-fusion (quote ℕ)

unquoteDecl foldℕ-fusion = defineInd foldℕ-fusionP foldℕ-fusion
-- foldℕ-fusion :
--     {X : Set ℓ} {Y : Set ℓ'} (h : X → Y)
--     {z : X} {s : X → X} {z' : Y} {s' : Y → Y}
--   → h z ≡ z' → ((x : X) (y : Y) → h x ≡ y → h (s x) ≡ s' y)
--   → (n : ℕ) → h (foldℕ z s n) ≡ foldℕ z' s' n
-- foldℕ-fusion h hz hs  zero   = hz
-- foldℕ-fusion h hz hs (suc n) = hs _ _ (foldℕ-fusion h hz hs n)

instance foldℕ-fusionC = genIndC foldℕ-fusionP foldℕ-fusion

--------
-- Induction operator

private
  indℕP : IndP
  indℕP = ind-operator (quote ℕ)

unquoteDecl indℕ = defineInd indℕP indℕ
-- indℕ : {P : ℕ → Set ℓ} → P 0 → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
-- indℕ z s  zero   = z
-- indℕ z s (suc n) = s n (indℕ z s n)

instance indℕC = genIndC indℕP indℕ
