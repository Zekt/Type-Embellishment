{-# OPTIONS -v meta:5 #-}
open import Prelude
open import Utils.Reflection

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

cxtToTel' : List (Arg Type) → Term
cxtToTel' [] = quoteTerm Tel'.∅
cxtToTel' (x ∷ cxt) =
  let tel = cxtToTel' cxt
  in  (con (quote Tel'._◁_) (x ∷ vArg (vLam (abs "" tel)) ∷ []))

cxtToTel : {ℓ : Level} → List (Arg Type) → TC (Tel' ℓ)
cxtToTel cxt = unquoteTC $ cxtToTel' cxt

--cxtToTel : List (Arg Type) → TC (Σ Level λ ℓ → Tel' ℓ)
--cxtToTel [] = return (_ , ∅)
--cxtToTel (arg i x ∷ cxt) = do
--  a ← unquoteTC {A = Set _} x
--  dprint [ strErr $ showTerm x ]
--  extendContext (vArg x) $ do
--    (_ , tel') ← cxtToTel cxt
--    qtel' ← quoteTC tel' >>= normalise
--    let lqtel' = lam visible (abs "" qtel')
--    tel'' ← unquoteTC {A = a → Tel' _} lqtel'
--    return (_ , a ◁ tel'')

--data Rel (A : Set) : List A → List A → Set
rel : Tel' _
rel = Set    ◁ λ A →
      List A ◁ λ _ →
      List A ◁ λ _ →
      ∅

rel' : List (Arg Type)
rel' = vArg (quoteTerm Set) ∷
       vArg (def (quote List) [ vArg (var 0 []) ]) ∷
       vArg (def (quote List) [ vArg (var 1 []) ]) ∷
       []

pointwise : Tel' _
pointwise = Set           ◁ λ A →
            Set           ◁ λ B →
            (A → B → Set) ◁ λ _ →
            List A        ◁ λ _ →
            List B        ◁ λ _ →
            ∅

--unquoteDecl = telToCxt pointwise >> return tt
unquoteDecl = cxtToTel rel' >>= λ rel →
              quoteTC rel   >>= λ x →
              dprint [ strErr $ showTerm x ]
