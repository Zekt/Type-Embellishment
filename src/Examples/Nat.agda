{-# OPTIONS --safe --without-K #-}

module Examples.Nat where

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

foldℕP : FoldP
foldℕP = fold-operator (quote ℕ)

-- unquoteDecl foldℕ = defineFold (fold-operator NatC) foldℕ
foldℕ : {X : Set ℓ} → X → (X → X) → ℕ → X
foldℕ z s  zero   = z
foldℕ z s (suc n) = s (foldℕ z s n)

foldℕT = genFoldT (fold-operator (quote ℕ)) foldℕ

instance
  foldℕC : FoldC (fold-operator (quote ℕ)) foldℕT
  FoldC.equation foldℕC (inl           refl  ) = refl
  FoldC.equation foldℕC (inr (inl (_ , refl))) = refl

foldℕ-fusionP : IndP
foldℕ-fusionP = fold-fusion (quote ℕ)

-- foldℕ-fusion :
--     {X : Set ℓ} {Y : Set ℓ'} (h : X → Y) (z : X) (s : X → X) (z' : Y) (s' : Y → Y)
--   → h z ≡ z' → ((x : X) (y : Y) → h x ≡ y → h (s x) ≡ s' y)
--   → (n : ℕ) → h (foldℕ z s n) ≡ foldℕ z' s' n
-- foldℕ-fusion h z s z' s' hz hs  zero   = hz
-- foldℕ-fusion h z s z' s' hz hs (suc n) =
--   hs (foldℕ z s n) (foldℕ z' s' n) (foldℕ-fusion h z s z' s' hz hs n)

-- foldℕ-fusionC = genIndC (fold-fusion NatC foldℕC) foldℕ-fusion

-- --------
-- -- Induction operator

-- -- unquoteDecl indℕ = defineInd (ind-operator NatC) indℕ
-- indℕ : {P : ℕ → Set ℓ} → P 0 → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
-- indℕ z s  zero   = z
-- indℕ z s (suc n) = s n (indℕ z s n)

-- indℕC = genIndC (ind-operator NatC) indℕ
