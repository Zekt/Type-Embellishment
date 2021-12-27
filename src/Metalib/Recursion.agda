{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Prelude

module Metalib.Recursion where

open import Utils.Reflection

open import Generics.Description as D
open import Generics.Algebra     as D
open import Generics.Recursion   as D

private
  pattern `inl x = con₁ (quote inl) x
  pattern `inr x = con₁ (quote inr) x
  pattern `refl  = con₀ (quote refl)
  pattern _`,_ x y = con₂ (quote Prelude._,_) x y

cxtToVars : (Γ : Telescope) → Pattern × Args Pattern
cxtToVars = snd ∘ foldr (0 , `refl , []) λ where
  (_ , arg i _) (n , p , args) → suc n , (var n `, p) , (arg i (var n) ∷ args)

mutual
  -- move this to Utils.Reflection if fixed
  fromPattern : Pattern → Term
  fromPattern (con c ps) = con c (fromPatterns ps)
  fromPattern (dot t)    = t
  fromPattern (var x)    = var₀ x
  fromPattern (lit l)    = lit l
  fromPattern (proj f)   = def₀ f
  -- incorrect for projections
  fromPattern (absurd x) = var₀ x
  -- incorrect for projections

  fromPatterns : Args Pattern → Args Term
  fromPatterns []             = []
  fromPatterns (arg i p ∷ ps) = arg i (fromPattern p) ∷ fromPatterns ps

forgetTypes : Telescope → Telescope
forgetTypes = map $ bimap id (λ `A → arg (getArgInfo `A) unknown)

module _ (pars : ℕ) where
  -- The telescope for parameters and the rest of it.
  splitConType : Type → Telescope
  splitConType `A = drop pars ((⇑ `A) .fst)

  conToClause : (c : Name) → TC (Telescope × Pattern × Args Pattern)
  conToClause c = < forgetTypes , cxtToVars > ∘ splitConType <$> getType c

  consToClauses : (cs : Names) → TC (List (Telescope × Pattern × Name × Args Pattern))
  consToClauses []       = ⦇ [] ⦈
  consToClauses (c ∷ cs) = do
    `Γ , p , args ← conToClause c
    cls  ← consToClauses cs
    return $ (`Γ , `inl p , c , args) ∷
      map (λ { (`Γ , p , c , args) → `Γ , `inr p , c , args}) cls

module _ (pars : ℕ) (cs : Names) where
  genFromCons :  (Telescope × Pattern × Name × Args Pattern → Clause) → TC Clauses
  genFromCons f = map f <$> consToClauses pars cs

  genToN : TC Term
  genToN = pat-lam₀ <$> genFromCons λ where
    (`Γ , p , c , args) → `Γ ⊢ [ vArg p ] `=
      con c (duplicate pars (hArg unknown) <> (fromPattern <$> args))

  genFromN-toN : TC Term
  genFromN-toN = pat-lam₀ <$> genFromCons λ where
    (Γ , p , _ , _) → Γ ⊢ [ vArg p ] `= `refl

  genFromN : TC Term
  genFromN = pat-lam₀ <$> genFromCons λ where
    (Γ , p , c , args) → Γ ⊢ [ vArg (con c args) ] `= fromPattern p

  genToN-fromN : TC Term
  genToN-fromN = pat-lam₀ <$> genFromCons λ where
    (Γ , p , c , args) → Γ ⊢ [ vArg (con c args) ] `= `refl
  
genDataC : (D : DataD) → (Nᶜ : DataTᶜ D) → Tactic
genDataC D Nᶜ hole = do
  hLam (abs "ℓs" t@(def d args)) ← quoteωTC (λ {ℓs} → Nᶜ {ℓs})
    where t → typeError (termErr t ∷ strErr " is not a definition." ∷ [])
  hole ← checkType hole =<< quoteTC (DataCᶜ D Nᶜ)

  pars , cs ← getDataDefinition d

  `toN       ← genToN       pars cs
  `fromN     ← genFromN     pars cs 
  `fromN-toN ← genFromN-toN pars cs 
  `toN-fromN ← genToN-fromN pars cs 

  unify hole $ con₄ (quote dataC) `toN `fromN `fromN-toN `toN-fromN

macro
  genToNT : Name → Tactic
  genToNT d hole = do
    pars , cs ← getDataDefinition d
    genToN pars cs >>= unify hole

  genFromN-toNT : Name → Tactic
  genFromN-toNT d hole = do
    pars , cs ← getDataDefinition d
    genFromN-toN pars cs >>= unify hole

  genFromNT : Name → Tactic
  genFromNT d hole = do
    pars , cs ← getDataDefinition d
    genFromN pars cs >>= unify hole

  genToN-fromNT : Name → Tactic
  genToN-fromNT d hole = do
    pars , cs ← getDataDefinition d
    genToN-fromN pars cs >>= unify hole

  genDataCT : (D : DataD) → (Nᶜ : DataTᶜ D) → Tactic
  genDataCT = genDataC
