{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Prelude

module Metalib.Recursion where

open import Utils.Reflection

open import Generics.Telescope   as D
open import Generics.Description as D
open import Generics.Levels      as D
open import Generics.Algebra     as D
open import Generics.Recursion   as D

open import Metalib.Telescope    as M
open import Metalib.Datatype     as M

private
  pattern `inl x = con₁ (quote inl) x
  pattern `inr x = con₁ (quote inr) x
  pattern `refl  = con₀ (quote refl)
  pattern _`,_ x y = con₂ (quote _,_) x y

module _ (pars : ℕ) where
  -- Γ is the telescope of a constructor (without parameters and indices)
  cxtToCurriedVars : (Γ : Telescope) → Telescope × Pattern × Args Term
  cxtToCurriedVars Γ = let _ , p , args = go Γ in
    (bimap id (const $ vArg unknown) <$> Γ) , p , unknowns <> args
    where
      go : (Γ : Telescope) → ℕ × Pattern × Args Term
      go = foldr (0 , `refl , []) λ where
        (_ , arg i _) (n , p , args) → suc n , (var n `, p) , arg i (var₀ n) ∷ args
      unknowns = duplicate pars (hArg unknown)

  conTypeToTelescope : Type → Telescope
  conTypeToTelescope `A = drop pars $ (⇑ `A) .fst

  conToClause : (c : Name) → TC (Telescope × Pattern × Args Term)
  conToClause c = cxtToCurriedVars ∘ conTypeToTelescope <$> getType c

  consToClauses : (cs : List Name) → TC (List (Telescope × Pattern × Name × Args Term))
  consToClauses []       = ⦇ [] ⦈
  consToClauses (c ∷ cs) = do
    `Γ , p , args ← conToClause c
    cls           ← map (bimap id (bimap `inr id)) <$> consToClauses cs
    return $ (`Γ , `inl p , c , args) ∷ cls

getDataDefinition : Name → TC (ℕ × Names)
getDataDefinition d = do
  data-type pars cs ← getDefinition d
    where _ → typeError (nameErr d ∷ strErr " is not a datatype." ∷ [])
  return $ pars , cs

genFromConDs : (Telescope × Pattern × Name × Args Term → Clause) → (d : Name) → TC Term
genFromConDs f d = do
  pars , cs ← getDataDefinition d
  pat-lam₀ ∘ map f <$> consToClauses pars cs


module _ (pars : ℕ) where
  cxtToUncurriedVars : (Γ : Telescope) → Telescope × Args Pattern × Term
  cxtToUncurriedVars Γ = let _ , args , t = go Γ in
    (bimap id (const $ vArg unknown) <$> Γ) , args , t
    where
      go : (Γ : Telescope) → ℕ × Args Pattern × Term
      go = foldr (0 , [] , `refl) λ where
        (_ , arg i _) (n , args , t) → suc n , arg i (var n) ∷ args , (var₀ n `, t)
        
  conToClause′ : (c : Name) → TC (Telescope × Args Pattern × Term)
  conToClause′ c = cxtToUncurriedVars ∘ conTypeToTelescope pars <$> getType c

  consToClauses′ : (cs : List Name) → TC (List (Telescope × Args Pattern × Name × Term))
  consToClauses′ []       = ⦇ [] ⦈
  consToClauses′ (c ∷ cs) = do
    `Γ , args , t ← conToClause′ c
    cls           ← map (λ { (`Γ , args , c , t) → `Γ , args , c , `inr t }) <$> consToClauses′ cs
    return $ (`Γ , args , c , `inl t) ∷ cls

genFromCons : (Telescope × Args Pattern × Name × Term → Clause) → (d : Name) → TC Term
genFromCons f d = do
  pars , cs ← getDataDefinition d
  pat-lam₀ ∘ map f <$> consToClauses′ pars cs

genToN : (d : Name) → TC Term
genToN = genFromConDs (λ { (Γ , p , c , args) → Γ ⊢ [ vArg p ] `= con c args })

genFromN-toN : (d : Name) → TC Term
genFromN-toN = genFromConDs (λ { (Γ , p , _ , _) → Γ ⊢ [ vArg p ] `= `refl })

genFromN : (d : Name) → TC Term
genFromN = genFromCons (λ { (Γ , args , c , t) → Γ ⊢ [ vArg (con c args) ] `= t })

genToN-fromN : (d : Name) → TC Term
genToN-fromN = genFromCons (λ { (Γ , args , c , t) → Γ ⊢ [ vArg (con c args) ] `= `refl })
  
genDataC : (D : DataD) → (Nᶜ : DataTᶜ D) → Tactic
genDataC D Nᶜ hole = do
  hLam (abs "ℓs" t@(def d args)) ← quoteωTC (λ {ℓs} → Nᶜ {ℓs})
    where t → typeError (termErr t ∷ strErr " is not a definition." ∷ [])

  `toN       ← genToN d 
  `fromN     ← genFromN d 
  `fromN-toN ← genFromN-toN d 
  `toN-fromN ← genToN-fromN d 

  checkedHole ← checkType hole =<< quoteTC (DataCᶜ D Nᶜ)
  unify checkedHole $ con₄ (quote dataC) `toN `fromN `fromN-toN `toN-fromN

macro
  genToNT : Name → Tactic
  genToNT c hole = genToN c >>= unify hole

  genFromN-toNT : Name → Tactic
  genFromN-toNT c hole = genFromN-toN c >>= unify hole

  genFromNT : Name → Tactic
  genFromNT c hole = genFromN c >>= unify hole

  genToN-fromNT : Name → Tactic
  genToN-fromNT c hole = genToN-fromN c >>= unify hole

  genDataCT : (D : DataD) → (Nᶜ : DataTᶜ D) → Tactic
  genDataCT D Nᶜ = genDataC D Nᶜ
