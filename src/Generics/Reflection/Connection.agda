{-# OPTIONS --safe --without-K #-}
open import Prelude

module Generics.Reflection.Connection where

open import Utils.Reflection
open import Utils.Error as Err

open import Generics.Description
open import Generics.Recursion  
open import Generics.Algebra

open import Generics.Reflection.Telescope
open import Generics.Reflection.Uncurry

private
  pattern `DataC x y     = def₂ (quote DataC) x y
  pattern `datac a b c d = con₄ (quote datac) a b c d

module _ (pars : ℕ) where
  conToClause : (c : Name) → TC (Telescope × (Term × Pattern) × Args Term × Args Pattern)
  conToClause c = < forgetTypes , cxtToVars 0 (`refl , `refl) > <$> getConTelescope c pars

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

    genToNT genFromN-toNT genFromNT genToN-fromNT : TC Term
    genToNT = pat-lam₀ <$> genFromCons λ where
      (`Γ , (_ , p) , c , args , _) → `Γ ⊢ [ vArg p ] `=
        con c (hUnknowns pars <> args)
    genFromN-toNT = pat-lam₀ <$> genFromCons λ where
      (Γ , (_ , p) , _ , _) → Γ ⊢ [ vArg p ] `= `refl
    genFromNT = pat-lam₀ <$> genFromCons λ where
      (Γ , (t , _) , c , _ , args) → Γ ⊢ [ vArg (con c args) ] `= t
    genToN-fromNT = pat-lam₀ <$> genFromCons λ where
      (Γ , _ , c , _ , args) → Γ ⊢ [ vArg (con c args) ] `= `refl
  
genDataCT : (D : DataD) → (d : Name) → Tactic
genDataCT D d hole = do
  `D ← quoteωTC D
  n  ← extendContextℓs #levels λ ℓs → length <$> fromTel (PDataD.Param (applyL ℓs))
  `N ← uncurryDataD D d

  checkedHole ← checkType hole (`DataC `D `N)
  
  pars , cs ← getDataDefinition d

  `toN       ← genToNT       pars cs
  `fromN     ← genFromNT     pars cs 
  `fromN-toN ← genFromN-toNT pars cs 
  `toN-fromN ← genToN-fromNT pars cs 

  noConstraints $ unify checkedHole $ `datac `toN `fromN `fromN-toN `toN-fromN
  where open DataD D

private
  fromData : (f : ℕ → Names → TC Term) → Name → Tactic
  fromData f d hole = getDataDefinition d >>= uncurry f >>= unify hole

macro
  genToN       = fromData genToNT
  genFromN-toN = fromData genFromN-toNT
  genFromN     = fromData genFromNT
  genToN-fromN = fromData genToN-fromNT

  genDataC : (D : DataD) → (d : Name) → Tactic
  genDataC = genDataCT
