open import Prelude

module Metalib.Example where

open import Metalib.Inductive-ConsTel 

open import Utils.Reflection
open import Generics.Description

--data Rel (A : Set) : List A → List A → Set
T-rel : Tel _
T-rel = [ A ∶ Set ] [ _ ∶ List A ] [ _ ∶ List A ] []
--rel = Set    ◁ λ A →
--      List A ◁ λ _ →
--      List A ◁ λ _ →
--      ∅

`T-rel : Context
`T-rel = vArg `Set₀ ∷
       vArg (def₁ `List (var₀ 0)) ∷
       vArg (def₁ `List (var₀ 1)) ∷
       []

T-rel' : Tel _
T-rel' = evalT (cxtToTel `T-rel) 

_ : T-rel' ≡ T-rel
_ = refl

pointwise : Tel _
pointwise = [ A ∶ Set ] [ B ∶ Set ] [ R ∶ (A → B → Set) ] [ _ ∶ List A ] [ _ ∶ List B ] []
{-
            Set           ◁ λ A →
            Set           ◁ λ B →
            (A → B → Set) ◁ λ _ →
            List A        ◁ λ _ →
            List B        ◁ λ _ →
            ∅
-}


Γ-pointwise : Context
Γ-pointwise = evalT (telToCxt pointwise) 

pointwise′ : Tel _
pointwise′ = evalT (cxtToTel Γ-pointwise) 

_ : pointwise′ ≡ pointwise
_ = refl

not-so-bad : Tel _
not-so-bad = [ b ∶ if true then Bool else ⊥ ] [] 

`not-so-bad : Context
`not-so-bad = evalT (telToCxt not-so-bad)

not-so-bad′ : Tel _
not-so-bad′ = evalT (cxtToTel `not-so-bad)

_ : Set
_ = evalT (unquoteTC (quoteTerm (if true then Bool else ⊥)))
