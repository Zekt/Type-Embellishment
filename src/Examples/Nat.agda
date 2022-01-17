{-# OPTIONS --safe --without-K #-}

module Examples.Nat where

open import Prelude
open import Generics.Telescope
open import Generics.Description
open import Generics.RecursionScheme
open import Metalib.Datatype
open import Metalib.Connection
open import Metalib.Recursion
open import Utils.Reflection

NatD = genDataD ℕ
NatC = genDataC NatD ℕ
-- [TODO] datatype wrapper

-- [TODO] print function definitions directly
-- [TODO] fold wrapper & connection
unquoteDecl foldℕ = defineFold (fold-operator NatC) foldℕ
