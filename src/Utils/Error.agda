{-# OPTIONS --without-K #-}

open import Prelude
open import Utils.Reflection

module Utils.Error where

variable
  A : Set ℓ

notEndIn : Name → TC A
notEndIn n = typeError (strErr "recursion does not end in "
                       ∷ nameErr n
                       ∷ [])

#idxNotMatch : TC A
#idxNotMatch = typeError [ strErr "number of indices doesn't match." ]

notλ : Term → TC A
notλ t = typeError $ strErr (show t) ∷ strErr " cannot be reduced further to a λ-abstraction" ∷ []

IMPOSSIBLE : TC A
IMPOSSIBLE = typeError $ [ strErr "An impossible event occurs." ]

IMPOSSIBLE-term : Term → TC A
IMPOSSIBLE-term t = typeError $ termErr t ∷ [ strErr " should not occur" ]
