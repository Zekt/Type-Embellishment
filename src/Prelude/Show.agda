module Prelude.Show where

------------------------------------------------------------------------------
open import Reflection.Show
------------------------------------------------------------------------------

open import Agda.Builtin.String 
open import Agda.Builtin.Sigma 
open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Reflection

record Show {a} (A : Set a) : Set a where
  field
    show : A → String
open Show ⦃...⦄ public

instance
  ShowString : Show String
  show {{ ShowString }} = primShowString

  ShowChar : Show Char
  show {{ ShowChar }} = primShowChar

  ShowNat : Show Nat
  show {{ ShowNat }} = primShowNat

  ShowTerm : Show Term
  show {{ ShowTerm }} = showTerm

  ShowTerms : Show (List (Arg Term))
  show {{ ShowTerms }} = showTerms

  ShowTel : Show (List (Σ String λ _ → Arg Type))
  show {{ ShowTel }} = showTel

  ShowClauses : Show _
  show {{ ShowClauses }} = showClauses
  
