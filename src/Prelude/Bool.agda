{-# OPTIONS --safe #-}
module Prelude.Bool where

open import Agda.Builtin.Unit
open import Prelude.Empty
open import Prelude.Eq

open import Agda.Builtin.Bool public

infixr 6 _∧_
infixr 5 _∨_ _xor_

instance
  EqBool : Eq Bool
  _==_ ⦃ EqBool ⦄ true  true  = true
  _==_ ⦃ EqBool ⦄ false false = true
  _==_ ⦃ EqBool ⦄ _     _     = false
  
not : Bool → Bool
not true  = false
not false = true

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ b = false

_∨_ : Bool → Bool → Bool
true  ∨ b = true
false ∨ b = b

_xor_ : Bool → Bool → Bool
true  xor b = not b
false xor b = b

infix  0 if_then_else_

if_then_else_ : ∀ {a} {A : Set a}
  → Bool → A → A → A
if true  then t else f = t
if false then t else f = f

T : Bool → Set
T false = ⊥
T true  = ⊤
