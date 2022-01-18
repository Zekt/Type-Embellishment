{-# OPTIONS --safe --without-K --show-implicit #-}

module Examples.Nat where

open import Prelude

open import Generics.Telescope
open import Generics.Description
open import Generics.Reflection

open import Generics.RecursionScheme

NatD = genDataD ℕ

-- [TODO] datatype wrapper

NatC = genDataC NatD ℕ  -- [FIXME]

-- [TODO] print function definitions directly

-- [TODO] fold wrapper & connection
unquoteDecl foldℕ = defineFold (fold-operator NatC) foldℕ  -- [FIXME]
-- [TODO] fold fusion

-- [TODO] induction operator
