{-# OPTIONS --without-K --safe #-}
module Prelude.Relation where
  
open import Prelude.Relation.Dec                    public
open import Prelude.Relation.PropositionalEquality  public

open import Prelude.Function
open import Prelude.Bool

private variable
  A B C : Set _

¬-reflects : ∀ {b ℓ} {P : Set ℓ} → Reflects P b → Reflects (¬ P) (not b)
¬-reflects (ofʸ  p) = ofⁿ (_$ p)
¬-reflects (ofⁿ ¬p) = ofʸ ¬p

¬? : ∀ {ℓ} {P : Set ℓ}
  → Dec P → Dec (¬ P)
does  (¬? p?) = not (does p?)
proof (¬? p?) = ¬-reflects (proof p?)

decEq₂ : {f : A → B → C}
  → (∀ {x y z w} → f x y ≡ f z w → x ≡ z)
  → (∀ {x y z w} → f x y ≡ f z w → y ≡ w)
  → ∀ {x y z w} → Dec (x ≡ y) → Dec (z ≡ w) → Dec (f x z ≡ f y w)
decEq₂ f-inj₁ f-inj₂ (no neq)    _         = no λ eq → neq (f-inj₁ eq)
decEq₂ f-inj₁ f-inj₂  _         (no neq)   = no λ eq → neq (f-inj₂ eq)
decEq₂ f-inj₁ f-inj₂ (yes refl) (yes refl) = yes refl
