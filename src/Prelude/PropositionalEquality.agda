module Prelude.PropositionalEquality where

open import Agda.Primitive
open import Agda.Builtin.Equality public

private variable
  a b c : Level
  A B C : Set a
  
cong : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ (f : A → B → C) {x y u v}
  → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

subst : {A : Set a} (P : A → Set b) {x y : A} → x ≡ y → P x → P y
subst P refl p = p
