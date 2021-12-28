{-# OPTIONS --without-K #-}
open import Prelude

module Metalib.Recursion where

open import Utils.Reflection

open import Generics.Description as D
open import Generics.Recursion   as D

private
  pattern `inl x = con₁ (quote inl) x
  pattern `inr x = con₁ (quote inr) x
  pattern `refl  = con₀ (quote refl)
  pattern _`,_ x y = con₂ (quote Prelude._,_) x y

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
