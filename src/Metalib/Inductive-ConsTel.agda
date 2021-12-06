{-# OPTIONS -v meta:5 #-}
open import Level
open import Prelude
open import Reflection
open import Agda.Builtin.Reflection

open import Generics.Description

module Metalib.Inductive-ConsTel where

dprint = debugPrint "meta" 5

telToCxt : {ℓ : Level} → (tel : Tel' ℓ)
          → TC (List (Arg Type))
telToCxt ∅ = return []
telToCxt (A ◁ tel) = do
  a ← quoteTC A
  dprint [ strErr $ showTerm a ]
  extendContext (vArg a) $ do
    a' ← unquoteTC {A = A} (var 0 [])
    tel' ← telToCxt (tel a')
    return (vArg a ∷ tel')

--data Rel (A : Set) : List A → List A → Set
rel : Tel' _
rel = Set    ◁ λ A →
      List A ◁ λ _ →
      List A ◁ λ _ →
      ∅

pointwise : Tel' _
pointwise = Set ◁ λ A →
            Set ◁ λ B →
            (A → B → Set) ◁ λ r →
            List A ◁ λ _ →
            List B ◁ λ _ →
            ∅

unquoteDecl = telToCxt pointwise >> return tt
