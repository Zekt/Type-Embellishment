{-# OPTIONS --safe #-}

module Prelude.Class.DecEq where

open import Agda.Builtin.Equality

open import Prelude.Class.Equality
open import Prelude.Relation.Dec

record DecEq {a} (A : Set a) : Set a where
  infix 4 _≟_
  field
    _≟_  : (x y : A) → Dec (x ≡ y)
open DecEq ⦃...⦄ public

{-# DISPLAY DecEq._≟_  _ = _≟_  #-}
