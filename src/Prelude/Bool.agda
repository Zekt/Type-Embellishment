module Prelude.Bool where

open import Agda.Builtin.Bool public

infixr 6 _∧_
infixr 5 _∨_ _xor_

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
