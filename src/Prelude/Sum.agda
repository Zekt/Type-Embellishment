{-# OPTIONS --without-K --safe #-}
module Prelude.Sum where

open import Agda.Primitive

infixr 1 _⊎_

data _⊎_ {a} {b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inl : (x : A) → A ⊎ B
  inr : (y : B) → A ⊎ B

[_,_] : ∀ {a b c} {A : Set a} {B : Set b} {C : A ⊎ B → Set c} →
        ((x : A) → C (inl x)) → ((x : B) → C (inr x)) →
        ((x : A ⊎ B) → C x)
[ f , g ] (inl x) = f x
[ f , g ] (inr y) = g y

data _⊎ω_ {a} (A : Set a) (B : Setω) : Setω where
  inl : (x : A) → A ⊎ω B
  inr : (y : B) → A ⊎ω B

[_,_]ω : ∀ {a c} {A : Set a} {B : Setω} {C : A ⊎ω B → Set c} →
        ((x : A) → C (inl x)) → ((x : B) → C (inr x)) →
        ((x : A ⊎ω B) → C x)
[ f , g ]ω (inl x) = f x
[ f , g ]ω (inr y) = g y
