{-# OPTIONS -v meta:5 #-}

open import Prelude

module Metalib.Inductive-ConsTel where

open import Utils.Reflection
open import Generics.Description
  using (Tel'; _◁_; ∅)

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
  `A ← quoteTC! A
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
