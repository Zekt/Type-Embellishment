{-# OPTIONS --without-K --safe #-}

open import Prelude

module Utils.Error where

open import Utils.Reflection.Core
open import Utils.Reflection.Show

private variable
  A : Set _

notEndIn : String → Name → TC A
notEndIn s n = typeError (strErr "Type of"
                       ∷ strErr s
                       ∷ strErr "does not end in "
                       ∷ nameErr n
                       ∷ [])

#idxNotMatch : TC A
#idxNotMatch = typeError [ strErr "number of indices doesn't match." ]

notλ : Term → TC A
notλ t = typeError $ strErr (show t) ∷ strErr " cannot be reduced further to a λ-abstraction" ∷ []

notDef : Term → TC A
notDef t = typeError $ termErr t ∷ strErr " is not a definition." ∷ []

notFun : Name → TC A
notFun d = typeError $ nameErr d ∷ [ strErr " is not a function." ]

notData : Name → TC A
notData d = typeError $ nameErr d ∷ [ strErr " is not a datatype." ]

IMPOSSIBLE : TC A
IMPOSSIBLE = typeError $ [ strErr "An impossible event occurs." ]

IMPOSSIBLE-term : Term → TC A
IMPOSSIBLE-term t = typeError $ termErr t ∷ [ strErr " should not occur" ]
