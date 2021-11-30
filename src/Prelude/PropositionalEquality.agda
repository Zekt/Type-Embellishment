{-# OPTIONS --safe #-}
module Prelude.PropositionalEquality where

open import Agda.Primitive
open import Agda.Builtin.Equality public

private variable
  a b c : Level
  A B C : Set a

sym : {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq

cong : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ (f : A → B → C) {x y u v}
  → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

subst : {A : Set a} (P : A → Set b) {x y : A} → x ≡ y → P x → P y
subst P refl p = p
