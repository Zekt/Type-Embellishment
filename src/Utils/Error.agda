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
