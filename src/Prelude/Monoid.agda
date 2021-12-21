{-# OPTIONS --without-K --safe #-}

module Prelude.Monoid where

open import Agda.Builtin.String 

record Semigroup {a} (A : Set a) : Set a where
  infixr 5 _<>_
  field
    _<>_ : A → A → A
open Semigroup ⦃...⦄ public

record Monoid {a} (A : Set a) : Set a where
  field
    mempty            : A
    overlap ⦃ super ⦄ : Semigroup A
open Monoid ⦃...⦄ public

instance
  SemigroupString : Semigroup String
  _<>_ ⦃ SemigroupString ⦄ = primStringAppend
  
  MonoidString : Monoid String
  mempty ⦃ MonoidString ⦄ = ""
