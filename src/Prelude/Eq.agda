{-# OPTIONS --without-K --safe #-}

module Prelude.Eq where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat as Nat
  renaming (_==_ to primNatEquality)
open import Agda.Builtin.Float  
open import Agda.Builtin.Word   
open import Agda.Builtin.Char   
open import Agda.Builtin.String 
open import Agda.Builtin.List

record Eq {a} (A : Set a) : Set a where
  infix 4 _==_ _/=_
  field
    _==_ : (x y : A) → Bool

  _/=_ : A → A → Bool
  x /= y with x == y
  ... | false = true
  ... | true  = false
open Eq ⦃...⦄ public

{-# DISPLAY Eq._==_ _ = _==_ #-}

instance
  EqNat : Eq Nat
  _==_ ⦃ EqNat ⦄ = primNatEquality

  EqFloat : Eq Float
  _==_ ⦃ EqFloat ⦄ = primFloatEquality 

  EqWord64 : Eq Word64
  _==_ ⦃ EqWord64 ⦄ x y = primWord64ToNat x == primWord64ToNat y

  EqChar : Eq Char
  _==_ ⦃ EqChar ⦄ = primCharEquality 

  EqString : Eq String
  _==_ ⦃ EqString ⦄ = primStringEquality

