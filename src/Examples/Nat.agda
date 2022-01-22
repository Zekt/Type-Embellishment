{-# OPTIONS --safe --without-K #-}

module Examples.Nat where

open import Prelude

open import Generics.Telescope
open import Generics.Description
open import Generics.Reflection
open import Generics.Recursion

open import Generics.RecursionScheme

NatD = genDataD ℕ
NatT = genDataT NatD ℕ
NatC = genDataC NatD NatT

-- unquoteDecl foldℕ = defineFold (fold-operator NatC) foldℕ
foldℕ : {X : Set ℓ} → X → (X → X) → ℕ → X
foldℕ z s  zero   = z
foldℕ z s (suc n) = s (foldℕ z s n)

foldℕT = genFoldT (fold-operator NatC) foldℕ
foldℕC = genFoldC (fold-operator NatC) foldℕT

-- unquoteDecl foldℕ-fusion = defineInd (fold-fusion NatC foldℕC) foldℕ-fusion
foldℕ-fusion :
    {X : Set ℓ} {Y : Set ℓ'} (h : X → Y) (z : X) (s : X → X) (z' : Y) (s' : Y → Y)
  → h z ≡ z' → ((x : X) (y : Y) → y ≡ h x → h (s x) ≡ s' y)
  → (n : ℕ) → h (foldℕ z s n) ≡ foldℕ z' s' n
foldℕ-fusion h z s z' s' hz hs  zero   = trans hz refl
foldℕ-fusion h z s z' s' hz hs (suc n) =
  trans (hs (foldℕ z s n) (foldℕ z' s' n) (sym (foldℕ-fusion h z s z' s' hz hs n))) refl

foldℕ-fusionT = genIndT (fold-fusion NatC foldℕC) foldℕ-fusion
foldℕ-fusionC = genIndC (fold-fusion NatC foldℕC) foldℕ-fusionT

-- unquoteDecl indℕ = defineInd (ind-operator NatC) indℕ
indℕ : {P : ℕ → Set ℓ} → P 0 → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
indℕ z s  zero   = z
indℕ z s (suc n) = s n (indℕ z s n)

indℕT = genIndT (ind-operator NatC) indℕ
indℕC = genIndC (ind-operator NatC) indℕT
