{-# OPTIONS --safe --without-K #-}
open import Prelude

module Tests.Instance where

open import Utils.Reflection

open import Generics.Telescope
open import Generics.Description
open import Generics.Recursion
open import Generics.RecursionScheme

open import Generics.Reflection

record _Has_ (d : Name) (A : Setω) : Setω where
  constructor has
  field
    a : A

private
  pattern _`Has_ x y = def₂ (quote _Has_) x y
  pattern `has   x   = con₁ (quote has) x
  pattern `DataD     = def₀ (quote DataD)

find : ∀ (A : Setω) d ⦃ _ : d Has A ⦄ → A
find A d ⦃ has a ⦄ = a

macro
  _deriving_by_ : (d : Name) (`A : Term) (tac : Name → TC Term)
    → Tactic
  (d deriving `A by tac) hole = do
    `t ← tac d
    `d ← quoteTC d
    checkType hole (`d `Has `A) >>= unify (`has `t)

instance
  h = ℕ deriving DataD by reifyData

macro
  genDataTᵢ : (d : Name) ⦃ _ : d Has DataD ⦄ → Tactic
  genDataTᵢ d ⦃ has D ⦄ = genDataTT D d

NatT = genDataTᵢ ℕ
