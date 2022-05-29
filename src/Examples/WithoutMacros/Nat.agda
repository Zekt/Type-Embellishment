{-# OPTIONS --safe --without-K #-}

module Examples.WithoutMacros.Nat where

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

foldℕ : {ℓ : Level} {X : Set ℓ} (alg : X) (alg1 : (z : X) → X)
        (z : ℕ) →
        X
foldℕ {ℓ = ℓ} {X = X} alg alg₁ zero = alg
foldℕ {ℓ = ℓ} {X = X} alg alg₁ (suc n) = alg₁ (foldℕ {ℓ} {X} alg alg₁ n)

instance foldℕC = genFoldC foldℕP foldℕ

private
  foldℕ-fusionP : IndP
  foldℕ-fusionP = fold-fusion (quote ℕ)

foldℕ-fusion : {ℓ ℓ1 : Level} {X : Set ℓ} {Y : Set ℓ1}
               (h : (z : X) → Y) {f : X} {f1 : (z : X) → X} {g : Y}
               {g1 : (z : Y) → Y} (hom : _≡_ {ℓ1} {Y} (h f) g)
               (hom1
                : (xs : X) (ys : Y) (z : _≡_ {ℓ1} {Y} (h xs) ys) →
                  _≡_ {ℓ1} {Y} (h (f1 xs)) (g1 ys))
               (n : ℕ) →
               _≡_ {ℓ1} {Y} (h (foldℕ {ℓ} {X} f f1 n)) (foldℕ {ℓ1} {Y} g g1 n)
foldℕ-fusion {ℓ = ℓ} {ℓ1 = ℓ₁} {X = X} {Y = Y} h {f = f} {f1 = f₁} {g = g} {g1 = g₁} hom hom₁ zero = hom
foldℕ-fusion {ℓ = ℓ} {ℓ1 = ℓ₁} {X = X} {Y = Y} h {f = f} {f1 = f₁} {g = g} {g1 = g₁} hom hom₁ (suc n) = hom₁ (foldℕ {ℓ} {X} f f₁ n) (foldℕ {ℓ₁} {Y} g g₁ n) (foldℕ-fusion {ℓ} {ℓ₁} {X} {Y} h {f} {f₁} {g} {g₁} hom hom₁ n)

instance foldℕ-fusionC = genIndC foldℕ-fusionP foldℕ-fusion

--------
-- Induction operator

private
  indℕP : IndP
  indℕP = ind-operator (quote ℕ)

indℕ : {ℓ : Level} (P : (z : ℕ) → Set ℓ) (ind-case : P 0)
       (ind-case1 : (ns : ℕ) (z : P ns) → P (suc ns)) (n : ℕ) →
       P n
indℕ {ℓ = ℓ} P ind-case ind-case₁ zero = ind-case
indℕ {ℓ = ℓ} P ind-case ind-case₁ (suc n) = ind-case₁ n
                                            (indℕ {ℓ} P ind-case ind-case₁ n)

instance indℕC = genIndC indℕP indℕ
