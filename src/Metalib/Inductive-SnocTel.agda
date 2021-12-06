{-# OPTIONS -v meta:5 #-}

module Metalib.Inductive-SnocTel where

open import Prelude
open import Utils.Reflection

open import Generics.Description


dprint = debugPrint "meta" 5

lookupTel : ∀ {ℓ} → {tel : Tel ℓ} → ℕ → ⟦ tel ⟧ᵗ → Maybe (Set ℓ)
lookupTel {tel = ∅} _ _ = nothing
lookupTel {tel = _▷_ {ℓ} tel A} zero (⟦tel⟧ , A') =
  just (Lift ℓ (A ⟦tel⟧))
lookupTel {tel = _▷_ {ℓ' = ℓ'} tel A} (suc n) (⟦tel⟧ , A') =
  maybe′ (just ∘ Lift ℓ') nothing (lookupTel n ⟦tel⟧)

test : Name → TC _
test funName = do
  let lam = vLam (abs "z" (def (quote _+_) (vArg (var 0 []) ∷ vArg (quoteTerm 1) ∷ [])))
  let patlam = pat-lam [ clause [ ("z" , vArg (quoteTerm ℕ)) ]
                                [ vArg (var 0) ]
                                (def (quote _+_) (vArg (var 0 []) ∷ vArg (quoteTerm 1) ∷ []))
                       ]
                       [ vArg (quoteTerm 2) ]
  lam' ← checkType lam (quoteTerm (ℕ → ℕ))
  lamType ← inferType lam'
  dprint [ termErr lam' ]
  declareDef (vArg funName) lamType
  defineFun funName [ clause [] [] lam ]
  return tt

unquoteDecl patFun = test patFun

module _ (tel : Tel ℓ) (A : ⟦ tel ⟧ᵗ → Set ℓ') where
  namedA : Name → TC _
  namedA funName = do
    typeOfA ← quoteTC (⟦ tel ⟧ᵗ → Set ℓ')
    bodyOfA ← quoteTC A
    declareDef (vArg funName) typeOfA
    defineFun funName [ clause [] [] bodyOfA ]

varTuple' : ℕ → ℕ → Term
varTuple' m zero    = var m []
varTuple' m (suc n) = con (quote _,_)
                          (vArg (varTuple' m n) ∷
                           vArg (var (m ∸ (suc n)) [])   ∷
                           [])

varTuple : ℕ → Term
varTuple m = varTuple' m m

lamTerm' : ℕ → ℕ → Name → Term
lamTerm' m zero    funName = lam visible $ abs "_" (def funName [ vArg (varTuple m) ])
lamTerm' m (suc n) funName = let lamTerm' = lamTerm' m n funName
                              in (lam visible (abs "_" lamTerm'))

lamTerm : ℕ → Name → Term
lamTerm m = lamTerm' m m

-- λ {(_ , s) → List s}
-- λ t → λ s → A (t , s)

-- λ {((_ , s) , l) → List s}
-- λ t → λ s → λ l → A ((t , s) , l)

lengthᵗ : {ℓ : Level} → Tel ℓ → ℕ
lengthᵗ ∅ = 0
lengthᵗ (tel ▷ A) = suc (lengthᵗ tel)

removeAbs : ℕ → Term → TC Term
removeAbs (suc n) (lam _ (abs _ x)) = removeAbs n x
removeAbs zero    t                 = return t
removeAbs _ _ = typeError [ strErr "IMPOSSIBLE" ]

telToCxt : {ℓ : Level} → (tel : Tel ℓ)
         → TC (List (Arg Type))
telToCxt ∅ = return []
telToCxt (_▷_ {ℓ} {ℓ'} tel A) = do
  tel' ← telToCxt tel
  funA ← freshName ""
  namedA tel A funA
  t ← normalise (lamTerm (lengthᵗ tel) funA) >>=
      removeAbs (suc $ lengthᵗ tel)
  --dprint [ strErr $ showTerm t ]
  return (vArg t ∷ tel')

{--
pointwise : Tel _
pointwise = ∅ ▷ (λ _ → Set) ▷ (λ _ → Set)
              ▷ (λ p → let ((_ , A) , B) = p in A → B → Set)
              ▷ (λ p → let (((_ , A) , B) , R) = p in List A)
              ▷ λ p → let ((((_ , A) , B) , R) , _) = p in List B

unquoteDecl = telToCxt pointwise >> return tt
--}
