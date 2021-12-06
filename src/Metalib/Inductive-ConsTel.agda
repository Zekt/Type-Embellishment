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

-- 
telToCxt : Tel' ℓ → TC Context
telToCxt ∅       = return []
telToCxt (A ◁ T) = do
  `A ← quoteTC A
  dprint [ strErr $ show `A ]
  extendContext (vArg `A) do
    `Γ ← telToCxt ∘ T =<< unquoteTC (var₀ 0)
    return $ vArg `A ∷ `Γ

cxtToTel' : Context → Term
cxtToTel' []        = `∅
cxtToTel' (`A ∷ `Γ) =
  let `T = cxtToTel' `Γ
  in `A `◁ vArg (`λ `T)

cxtToTel : Context → TC (Tel' ℓ)
cxtToTel = unquoteTC ∘ cxtToTel'
    
--data Rel (A : Set) : List A → List A → Set
T-rel : Tel' _
T-rel = [ A ∶ Set ] [ _ ∶ List A ] [ _ ∶ List A ] ∅
--rel = Set    ◁ λ A →
--      List A ◁ λ _ →
--      List A ◁ λ _ →
--      ∅

`T-rel : Context
`T-rel = vArg `Set₀ ∷
       vArg (def₁ `List (var₀ 0)) ∷
       vArg (def₁ `List (var₀ 1)) ∷
       []

T-rel' : Tel' _
T-rel' = evalT (cxtToTel `T-rel)

_ : T-rel' ≡ T-rel
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

Γ-pointwise : Context
Γ-pointwise = evalT (telToCxt pointwise)
