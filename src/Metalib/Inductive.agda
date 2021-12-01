{-# OPTIONS -v meta:5 #-}
open import Level
open import Prelude
open import Reflection
open import Agda.Builtin.Reflection

open import Generics.Description

module Metalib.Inductive where

dprint = debugPrint "meta" 5

lookupTel : ∀ {ℓ} → {tel : Tel ℓ} → ℕ → ⟦ tel ⟧ᵗ → Maybe (Set ℓ)
lookupTel {tel = ∅} _ _ = nothing
lookupTel {tel = _▷_ {ℓ} tel A} zero (⟦tel⟧ , A') =
  just (Lift ℓ (A ⟦tel⟧))
lookupTel {tel = _▷_ {ℓ' = ℓ'} tel A} (suc n) (⟦tel⟧ , A') =
  maybe′ (just ∘ Lift ℓ') nothing (lookupTel n ⟦tel⟧)

--preappend : {ℓ ℓ' : Level} → (T : Tel ℓ) → Type
--          → TC (⟦ T ⟧ᵗ → Set ℓ')
--preappend {.lzero} ∅ t = unquoteTC t >>= return ∘ const
--preappend {.(ℓ ⊔ ℓ')} (_▷_ {ℓ} {ℓ'} tel A) t = {!!}
-- (unquoteTC t >>= λ t' → return λ {tt → t'})
--             --do t' ← unquoteTC t
--             --   return λ {tt → t'}

--append : {ℓ ℓ' : Level} → (T : Tel ℓ) → Type → TC (Tel (ℓ ⊔ ℓ'))
--append tel [t] = {!!}
--append ∅ [t] = do t' ← unquoteTC [t]
--                  return (∅ ▷ λ {tt → t'})
--append (tel ▷ A) [t] = {!!}

test : Name → TC _
test funName = do
  let lam = lam visible (abs "z" (def (quote _+_) (vArg (var 0 []) ∷ vArg (quoteTerm 1) ∷ [])))
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

module _ {ℓ ℓ' : Level} (tel : Tel ℓ) (A : ⟦ tel ⟧ᵗ → Set ℓ') where
  namedA : Name → TC _
  namedA funName = do
    typeOfA ← quoteTC (⟦ tel ⟧ᵗ → Set ℓ') >>= normalise
    bodyOfA ← quoteTC A >>= normalise
    declareDef (vArg funName) typeOfA
    defineFun funName [ clause [] [] bodyOfA ]

varTuple' : ℕ → ℕ → Term
varTuple' m zero    = var m []
varTuple' m (suc n) = con (quote _,_)
                          (vArg (varTuple' m n) ∷
                           vArg (var (m ∸ (Prelude.suc n)) [])   ∷
                           [])

varTuple : ℕ → Term
varTuple m = varTuple' m m

lamTerm' : ℕ → ℕ → Name → TC Term
lamTerm' m zero    funName = return $ lam visible $ abs "_" (def funName [ vArg (varTuple m) ])
lamTerm' m (suc n) funName = do lamTerm' ← lamTerm' m n funName
                                return (lam visible (abs "_" lamTerm'))

lamTerm : ℕ → Name → TC Term
lamTerm m = lamTerm' m m

-- λ {(_ , s) → List s}
-- λ t → λ s → A (t , s)

-- λ {((_ , s) , l) → List s}
-- λ t → λ s → λ l → A ((t , s) , l)

lengthᵗ : {ℓ : Level} → Tel ℓ → ℕ
lengthᵗ ∅ = 0
lengthᵗ (tel ▷ A) = Prelude.suc (lengthᵗ tel)

removeAbs : ℕ → Term → TC Term
removeAbs (suc n) (lam _ (abs _ x)) = removeAbs n x
removeAbs zero    t                 = return t
removeAbs _ _ = typeError [ strErr "IMPOSSIBLE" ]

telToCxt : {ℓ : Level} → (tel : Tel ℓ)
         → TC (List (Arg Type))
telToCxt ∅ = return []
telToCxt (_▷_ {ℓ} {ℓ'} tel A) = do
  tel' ← telToCxt tel
  funA ← freshName "funA"
  namedA tel A funA
  t ← lamTerm (lengthᵗ tel) funA >>=
      normalise                  >>=
      removeAbs (Prelude.suc $ lengthᵗ tel)
  dprint [ strErr $ showTerm t ]
  return (vArg t ∷ tel')
  --typeOfFunA ← getType funA
  --tTyp ← inferType t
  --inContext tel' $ do
  --  t ← quoteTC (A ⟦tel⟧)
  --  debugPrint "meta" 5 [ termErr t ]
  --  cxt ← getContext
  --  debugPrint "meta" 5 [ strErr $ showTerms cxt ]
    --if (0 <ᵇ (length tel'))
    --  then
    --    (unify m (var 0 []))
    --  else
    --    (return tt)
    --    (extendContext (vArg t) (unify m (var 0 [])))
    --extendContext (vArg t) $ do
    --  var0 ← unquoteTC (var 0 [])

data Rel (A : Set) : List A → List A → Set where

pt : Type
pt = pi (vArg (quoteTerm Set))
        (abs "_" (pi (vArg (def (quote List)
                                [ vArg (var 0 []) ]))
                     (abs "_" (def (quote List)
                                   [ vArg (var 1 []) ]))))

telt : Tel (lsuc lzero)
telt = ∅ ▷ (λ _ → Set)
         ▷ (λ { (_ , s) → List s})
         ▷ λ {((_ , s) , l) → List s}

telt' = ∅ ▷ (λ _ → Set) ▷ (λ { (_ , s) → List s})

A' : ⟦ telt' ⟧ᵗ → Set
A' = λ {((_ , s) , l) → List s}

--A'' : λ { (_ , s) → List s}

testTerm : TC _
testTerm = do funName ← freshName "funA"
              namedA telt' A' funName
              t ← lamTerm (lengthᵗ telt') funName
              -- t = λ z z₁ → Metalib.Inductive.funA ((tt , z₁) , z)
              -- t = λ z z₁ → List z
              --t' ← checkType t (quoteTerm (Set → ⊤ → Set))
              funNameType ← getType funName
              funNameTypeType ← inferType funNameType
              dprint [ termErr funNameType ]
              return tt


--unquoteDecl = testTerm

unquoteDecl = telToCxt telt >> return tt
