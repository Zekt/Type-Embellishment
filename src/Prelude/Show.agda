{-# OPTIONS --without-K --safe #-}
module Prelude.Show where

------------------------------------------------------------------------------

open import Agda.Builtin.String 
open import Agda.Builtin.Sigma 
open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.Float
open import Agda.Builtin.Word
open import Agda.Builtin.List
open import Agda.Builtin.Nat using (Nat)

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

  ShowFloat : Show Float
  show {{ ShowFloat }} = primShowFloat
  
  ShowWord64 : Show Word64
  show {{ ShowWord64 }} x = primShowNat (primWord64ToNat x)

--  ShowTerm : Show Term
--  show {{ ShowTerm }} = showTerm

--  ShowTerms : Show (List (Arg Term))
--  show {{ ShowTerms }} = showTerms

--  ShowTel : Show (List (Σ String λ _ → Arg Type))
--  show {{ ShowTel }} = showTel

--  ShowClauses : Show _
--  show {{ ShowClauses }} = showClauses
  
