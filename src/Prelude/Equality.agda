{-# OPTIONS --safe #-}
module Prelude.Equality where


import Data.Nat as ℕ
  using (_≟_)
open import Reflection.Term as R
  using (Term; Type; Clause; Clauses; Sort)
open import Reflection.Name
  using (Name)
  renaming (_≟_ to _≟-Name_)

open import Relation.Nullary
  using (Dec; does; no; yes; _because_)
  
------------------------------------------------------------------------------
-- Only built-in modules should be used.
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat as Nat
  using () renaming (Nat to ℕ)

record Eq {a} (A : Set a) : Set a where
  infix 4 _≟_ _==_
  field
    _≟_  : (x y : A) → Dec (x ≡ y)
    _==_ : (x y : A) → Bool
open Eq ⦃...⦄ public

{-# DISPLAY Eq._≟_  _ = _≟_  #-}
{-# DISPLAY Eq._==_ _ = _==_ #-}

instance
  NatEq : Eq ℕ
  _≟_  {{ NatEq }} = ℕ._≟_
  _==_ {{ NatEq }} = Nat._==_

  TermEq : Eq Term
  _≟_  {{ TermEq }} = R._≟_
  _==_ {{ TermEq }} x y = (x ≟ y) .does

  NameEq : Eq Name
  _≟_  {{ NameEq }} = _≟-Name_
  _==_ {{ NameEq }} x y = (x ≟ y) .does
