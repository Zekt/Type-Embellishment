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
open import Generics.Reflection.Recursion

private
  pattern `DataC x y     = def₂ (quote DataC) x y
  pattern `datac a b c d = con₄ (quote datac) a b c d
  pattern `FoldC x y     = def₂ (quote FoldC) x y
  pattern `IndC  x y     = def₂ (quote IndC)  x y

module _ (pars : ℕ) where
  conToClause : (c : Name) → TC (Telescope × Vars)
  conToClause c = < forgetTypes , cxtToVars 0 (`refl , `refl) > <$> getConTelescope c pars

  consToClauses : (cs : Names) → TC (List (Telescope × Name × Vars))
  consToClauses []       = ⦇ [] ⦈
  consToClauses (c ∷ cs) = do
    `Γ , (t , p) , args ← conToClause c
    cls                 ← consToClauses cs
    return $ (`Γ , c , (`inl t , `inl p) , args)
      ∷ ((λ { (`Γ , c , (t , p) , args) → `Γ , c , (`inr t , `inr p) , args}) <$> cls)

  module _ (cs : Names) where
    genFromCons :  (Telescope × Name × Vars → Clause) → TC Clauses
    genFromCons f = map f <$> consToClauses cs

    genToNT genFromN-toNT genFromNT genToN-fromNT : TC Term
    genToNT = pat-lam₀ <$> genFromCons λ where
      (`Γ , c , (_ , p) , args , _) → `Γ ⊢ [ vArg p ] `=
        con c (hUnknowns pars <> args)
    genFromN-toNT = pat-lam₀ <$> genFromCons λ where
      (Γ , _ , (_ , p) , _) → Γ ⊢ [ vArg p ] `= `refl
    genFromNT = pat-lam₀ <$> genFromCons λ where
      (Γ , c , (t , _) , _ , args) → Γ ⊢ [ vArg (con c args) ] `= t
    genToN-fromNT = pat-lam₀ <$> genFromCons λ where
      (Γ , c , _ , _ , args) → Γ ⊢ [ vArg (con c args) ] `= `refl

    genFoldC-equation = pat-lam₀ <$> genFromCons λ where
      (Γ , c , (_ , p) , _) → Γ ⊢ vArg (proj (quote (FoldC.equation))) ∷ vArg p ∷ [] `= `refl

    genIndC-equation = pat-lam₀ <$> genFromCons λ where
      (Γ , c , (_ , p) , _) → Γ ⊢ vArg (proj (quote (IndC.equation))) ∷ vArg p ∷ [] `= `refl
  
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

genFoldCT : (P : FoldP) (f : FoldGT P) → Tactic
genFoldCT P f hole = do
  `P ← quoteωTC P
  `f ← quoteωTC f
  hole ← checkType hole $ `FoldC `P `f
  d ← FoldPToNativeName P
  pars , cs ← getDataDefinition d
  genFoldC-equation pars cs  >>= unify hole
  
genIndCT : (P : IndP) (f : IndGT P) → Tactic
genIndCT P f hole = do
  `P ← quoteωTC P
  `f ← quoteωTC f 
  hole ← checkType hole $ `IndC `P `f
  d ← IndPToNativeName P
  pars , cs ← getDataDefinition d
  genIndC-equation pars cs  >>= unify hole

macro
  genDataC : (D : DataD) (d : Name) → Tactic
  genDataC = genDataCT

  genFoldC : (P : FoldP) (f : FoldGT P) → Tactic
  genFoldC = genFoldCT

  genIndC : (P : IndP) (f : IndGT P) → Tactic
  genIndC = genIndCT
