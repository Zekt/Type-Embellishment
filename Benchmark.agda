{-# OPTIONS --safe --without-K #-}

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

instance foldℕC = genFoldC foldℕP foldℕ

private
  foldℕ-fusionP : IndP
  foldℕ-fusionP = fold-fusion (quote ℕ)

unquoteDecl foldℕ-fusion = defineInd foldℕ-fusionP foldℕ-fusion

instance foldℕ-fusionC = genIndC foldℕ-fusionP foldℕ-fusion

--------
-- Induction operator

private
  indℕP : IndP
  indℕP = ind-operator (quote ℕ)

unquoteDecl indℕ = defineInd indℕP indℕ

instance indℕC = genIndC indℕP indℕ
