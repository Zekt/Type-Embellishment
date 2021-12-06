{-# OPTIONS --safe #-}
module Prelude.Relation.Dec where

open import Agda.Builtin.Bool
open import Prelude.Empty

------------------------------------------------------------------------
-- Negation.

infix 3 ¬_
infix 2 _because_

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ P = P → ⊥

------------------------------------------------------------------------
-- `Reflects` idiom.

-- The truth value of P is reflected by a boolean value.

data Reflects {p} (P : Set p) : Bool → Set p where
  ofʸ : ( p :   P) → Reflects P true
  ofⁿ : (¬p : ¬ P) → Reflects P false

record Dec {p} (P : Set p) : Set p where
  constructor _because_
  field
    does  : Bool
    proof : Reflects P does
open Dec public

pattern yes p =  true because ofʸ  p
pattern no ¬p = false because ofⁿ ¬p
