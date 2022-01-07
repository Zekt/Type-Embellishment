{-# OPTIONS --without-K #-}
open import Prelude

module Metalib.Recursion where

open import Utils.Reflection
open import Utils.Error as Err

open import Generics.Description     as D
open import Generics.Recursion       as D
open import Generics.RecursionScheme as D
open import Generics.Algebra         as D

private
  pattern `inl x = con₁ (quote inl) x
  pattern `inr x = con₁ (quote inr) x
  pattern `refl  = con₀ (quote refl)
  pattern _`,_ x y = con₂ (quote Prelude._,_) x y
  pattern `Algebra = quote Algebra

  -- c x₁ x₂ ⋯ xₙ can be represented as `Term` and `Pattern`
  cxtToVars : (Γ : Telescope) → (Term × Pattern) × (Args Term × Args Pattern)
  cxtToVars = snd ∘ foldr (0 , (`refl , `refl) , ([] , [])) λ where
    (_ , arg i _) (n , (t , p) , (targs , pargs)) →
      suc n , ((var₀ n `, t) , (var n `, p)) , (arg i (var₀ n) ∷ targs) , (arg i (var n) ∷ pargs)

module _ (pars : ℕ) where
  conToClause : (c : Name) → TC (Telescope × (Term × Pattern) × Args Term × Args Pattern)
  conToClause c = < forgetTy , cxtToVars > ∘ (λ `A → drop pars $ (⇑ `A) .fst) <$> getType c
    where forgetTy = map $ bimap id (λ `A → arg (getArgInfo `A) unknown)

  consToClauses : (cs : Names) → TC (List (Telescope × (Term × Pattern) × Name × Args Term × Args Pattern))
  consToClauses []       = ⦇ [] ⦈
  consToClauses (c ∷ cs) = do
    `Γ , (t , p) , args ← conToClause c
    cls                 ← consToClauses cs
    return $ (`Γ , (`inl t , `inl p) , c , args)
      ∷ ((λ { (`Γ , (t , p) , c , args) → `Γ , (`inr t , `inr p) , c , args}) <$> cls)

  module _ (cs : Names) where
    genFromCons :  (Telescope × (Term × Pattern) × Name × Args Term × Args Pattern → Clause) → TC Clauses
    genFromCons f = map f <$> consToClauses cs

    genToN genFromN-toN genFromN genToN-fromN : TC Term
    genToN = pat-lam₀ <$> genFromCons λ where
      (`Γ , (_ , p) , c , args , _) → `Γ ⊢ [ vArg p ] `=
        con c (hUnknowns pars <> args)
    genFromN-toN = pat-lam₀ <$> genFromCons λ where
      (Γ , (_ , p) , _ , _) → Γ ⊢ [ vArg p ] `= `refl
    genFromN = pat-lam₀ <$> genFromCons λ where
      (Γ , (t , _) , c , _ , args) → Γ ⊢ [ vArg (con c args) ] `= t
    genToN-fromN = pat-lam₀ <$> genFromCons λ where
      (Γ , _ , c , _ , args) → Γ ⊢ [ vArg (con c args) ] `= `refl
  
genDataC : (D : DataD) → (Nᶜ : DataTᶜ D) → Tactic
genDataC D Nᶜ hole = do
  hole ← checkType hole =<< quoteTC (DataCᶜ D Nᶜ)
  
  hLam (abs "ℓs" t@(def d args)) ← quoteωTC (λ {ℓs} → Nᶜ {ℓs})
    where t → typeError (termErr t ∷ strErr " is not a definition." ∷ [])
  pars , cs ← getDataDefinition d

  `toN       ← genToN       pars cs
  `fromN     ← genFromN     pars cs 
  `fromN-toN ← genFromN-toN pars cs 
  `toN-fromN ← genToN-fromN pars cs 

  unify hole $ con₄ (quote dataC) `toN `fromN `fromN-toN `toN-fromN

private
  fromData : (f : ℕ → Names → TC Term) → Name → Tactic
  fromData f d hole = getDataDefinition d >>= uncurry f >>= unify hole

macro
  genToNT       = fromData genToN
  genFromN-toNT = fromData genFromN-toN
  genFromNT     = fromData genFromN
  genToN-fromNT = fromData genToN-fromN

  genDataCT : (D : DataD) → (Nᶜ : DataTᶜ D) → Tactic
  genDataCT = genDataC

genFold : (D : DataD) → (Nᶜ : DataTᶜ D) → (C : DataCᶜ D Nᶜ)→ Name → Tactic
genFold D Nᶜ Cᶜ fun hole = do
  --let N = DataCᶜ D Nᶜ
  --algName ← freshName ""
  --let curriedAlgT : Type
  --    curriedAlgT = pi (hArg (quoteTerm Level))
  --                     {!!}
  --declareDef (vArg algName) {!!}
  qD ← quoteTC D
  `algT ← dontReduceDefs [ `Algebra ] $ inferType (def fun [ vArg qD ]) >>= normalise
  debugPrint "meta" 5 [ termErr `algT  ]
  unify hole (quoteTerm tt)
  where
    mutual
      replaceAlgAcc : List (Arg Term) → List (Arg Term) → List Name → Type → TC (List (Arg Term))
      replaceAlgAcc args [] ∀s taker = IMPOSSIBLE
      replaceAlgAcc args [ arg i x ] ∀s taker = do
        x' ← replaceAlg x ∀s taker
        return (args <> [ arg i x' ])
      replaceAlgAcc args (x ∷ xs) ∀s taker =
        replaceAlgAcc (args <> [ x ]) xs ∀s taker

      -- replace Algebra with FoldT in a function type,
      -- thus generate a type of fold-wrapper
      replaceAlg : Type → List Name → Type → TC Type
      replaceAlg (def `Algebra args) ∀s taker =
        let foldT = {!!}
        in  return (def (quote FoldT) {!!})
      replaceAlg (def m args) ∀s taker with elem m ∀s
      ... | true = do
        args' ← replaceAlgAcc [] args ∀s taker
        return (def m args')
      ... | _ = notEndIn "fold-alg" `Algebra
      replaceAlg (`Π[ s ∶ a ] x) ∀s taker = do
        x' ← replaceAlg x ∀s taker
        return (`Π[ s ∶ a ] x')
      replaceAlg _ _ _ = notEndIn "fold-alg" `Algebra

macro
  genFoldT = genFold
