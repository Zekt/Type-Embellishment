module Prelude.Relation where

open import Prelude.Function
open import Prelude.Empty
open import Prelude.Bool

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

¬-reflects : ∀ {b ℓ} {P : Set ℓ} → Reflects P b → Reflects (¬ P) (not b)
¬-reflects (ofʸ  p) = ofⁿ (_$ p)
¬-reflects (ofⁿ ¬p) = ofʸ ¬p

¬? : ∀ {ℓ} {P : Set ℓ}
  → Dec P → Dec (¬ P)
does  (¬? p?) = not (does p?)
proof (¬? p?) = ¬-reflects (proof p?)
