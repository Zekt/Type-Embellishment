{-# OPTIONS --without-K --safe #-}
module Prelude.Relation.PropositionalEquality where

open import Agda.Primitive
open import Agda.Builtin.Equality public

private variable
  a b c : Level
  A B C : Set _

sym : {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq

cong : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ (f : A → B → C) {x y u v}
  → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

subst : (P : A → Set b) {x y : A} → x ≡ y → P x → P y
subst P refl p = p

module ≡-Reasoning {A : Set a} where

  infix  3 _∎
  infixr 2 _≡⟨⟩_ step-≡ step-≡˘
  infix  1 begin_

  begin_ : ∀{x y : A} → x ≡ y → x ≡ y
  begin_ x≡y = x≡y

  _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
  step-≡ _ y≡z x≡y = trans x≡y y≡z

  step-≡˘ : ∀ (x {y z} : A) → y ≡ z → y ≡ x → x ≡ z
  step-≡˘ _ y≡z y≡x = trans (sym y≡x) y≡z

  _∎ : ∀ (x : A) → x ≡ x
  _∎ _ = refl

  syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z
  syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z

FunExt : Setω
FunExt = ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (a : A) → B a}
         → (∀ a → f a ≡ g a) → f ≡ g

infix 4 _≡ω_

data _≡ω_ {A : Setω} (x : A) : A → Setω where
  refl : x ≡ω x

substω₁ : {A : Setω} (P : A → Setω₁) {x y : A} → x ≡ω y → P x → P y
substω₁ P refl p = p

symω : {A : Setω} {x y : A} → x ≡ω y → y ≡ω x
symω refl = refl
