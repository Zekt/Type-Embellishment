{-# OPTIONS -v meta:5 #-}

open import Prelude
open import Utils.Reflection

open import Generics.Description

module Metalib.Inductive-ConsTel where

dprint = debugPrint "meta" 5

-- Frequently used terms
_`◁_ : Arg Term → Arg Term → Term
t `◁ u = con (quote Tel'._◁_) (t ∷ u ∷ [])

`∅ : Term
`∅ = quoteTerm Tel'.∅

`List : Name
`List = quote List

-- 
telToCxt : Tel' ℓ → TC Context
telToCxt ∅       = return []
telToCxt (A ◁ T) = do
  `A ← quoteTC A
  dprint [ strErr $ show `A ]
  extendContext (vArg `A) do
    x  ← unquoteTC {A = A} (var₀ 0)
    `Γ ← telToCxt (T x)
    return (vArg `A ∷ `Γ)

cxtToTel' : Context → Term
cxtToTel' []        = `∅
cxtToTel' (`A ∷ `Γ) =
  let T = cxtToTel' `Γ
  in `A `◁ vArg (`λ T)

cxtToTel : Context → TC (Tel' ℓ)
cxtToTel = unquoteTC ∘ cxtToTel'
    
--data Rel (A : Set) : List A → List A → Set
rel : Tel' _
rel = [ A ∶ Set ] [ _ ∶ List A ] [ _ ∶ List A ] ∅
--rel = Set    ◁ λ A →
--      List A ◁ λ _ →
--      List A ◁ λ _ →
--      ∅

rel' : Context
rel' = vArg `Set₀ ∷
       vArg (def₁ `List (var₀ 0)) ∷
       vArg (def₁ `List (var₀ 1)) ∷
       []

Trel' : Tel' _
Trel' = evalT (cxtToTel rel')

_ : Trel' ≡ rel
_ = refl

pointwise : Tel' _
pointwise = [ A ∶ Set ] [ B ∶ Set ] [ R ∶ (A → B → Set) ] [ _ ∶ List A ] [ _ ∶ List B ] ∅
{-
            Set           ◁ λ A →
            Set           ◁ λ B →
            (A → B → Set) ◁ λ _ →
            List A        ◁ λ _ →
            List B        ◁ λ _ →
            ∅
-}

unquoteDecl = telToCxt pointwise >> return tt
