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

private variable
  rb  : RecB
  cb  : ConB
  cbs : ConBs
------------------------------------------------------------------------
-- Terms

private
  `dataC : Term → Term → Term → Term → Term
  `dataC = con₄ (quote dataC)


  pattern `inl x = con₁ (quote inl) x
  pattern `inr x = con₁ (quote inr) x
  pattern `refl  = con₀ (quote refl)
  pattern _`,_ x y = con₂ (quote _,_) x y

------------------------------------------------------------------------
--
  getLevels : (D : DataD) → TC Type
  getLevels D = quoteTC {A = Set} Levels
    where open DataD D

-- Γ is the telescope of a constructor (without parameters and indices)
cxtToVars : (Γ : Telescope) → Telescope × Pattern × Args Term -- Arg Pattern × Args Term
cxtToVars Γ = let _ , p , args = go Γ in
  (bimap id (const $ vArg unknown) <$> Γ) , p , args
  where
    go : (Γ : Telescope) → ℕ × Pattern × Args Term
    go = foldr (0 , `refl , []) λ where
      (_ , arg i _) (n , p , args) → suc n , (var n `, p) , arg i (var₀ n) ∷ args
        
conTypeToTelescope : (pars : ℕ) → Type → Telescope
conTypeToTelescope pars `A = drop pars $ (⇑ `A) .fst

module _ (pars : ℕ) where
  conToClause : (c : Name) → TC (Telescope × Pattern × Args Term)
  conToClause c = cxtToVars ∘ conTypeToTelescope pars <$> getType c

  consToClauses : (cs : List Name) → TC (List $ Telescope × Pattern × Term)
  consToClauses []       = ⦇ [] ⦈
  consToClauses (c ∷ cs) = do
    `Γ , p , args ← conToClause c
    cls           ← map (λ { (`Γ , p , t) → `Γ , `inr p , t })  <$> consToClauses cs
    return $ (`Γ , `inl p , con c args) ∷ cls

genToN : (c : Name) → TC Term
genToN c = do
  data-type pars cs ← getDefinition c
    where _ → typeError (nameErr c ∷ strErr " is not a datatype." ∷ [] )
  pat-lam₀ ∘ map (λ { (`Γ , p , t) → clause `Γ [ vArg p ] t }) <$> consToClauses pars cs

-- module _ (D : DataD) (Nᶜ : DataTᶜ D) where
--   open DataD D

--   N : DataT D
--   N = uncurryᵈᵗ D Nᶜ

--   -- `gen-toN` generates a term of pattern matching lambda
--   gen-toN : Names → TC Term
--   gen-toN cs = extendContextℓs #levels λ ℓs → do
--     `Levels ← getLevels D
--     `Alg    ← hΠ[ "ℓs" ∶ `Levels ]_ <$> quoteTC (∀ {ps} → Algᵈ D (N ℓs ps))

--     let open PDataD (applyL ℓs)
--     extendContextTs Param λ ps → do
--       gen-toN-ConDs (applyP ps) cs
--       return tt
    
--     {!!}
--   {-
--     `Levels ← quoteTC {A = Set} Levels
--     `Alg ← hΠ[ "ℓs" ∶ `Levels ]_ <$> extendContextℓs #levels λ ℓs →
--       quoteTC (∀ {ps} → Algᵈ D (N ℓs ps))

--     define! `Alg (gen-toN-ConDs {!PDataD.applyP !} cs)
--   -}

--   gen-fromN : TC Term
--   gen-fromN = {!!}

--   gen-fromN-toN : TC Term
--   gen-fromN-toN = {!!}

--   gen-toN-fromN : TC Term
--   gen-toN-fromN = {!!}

--   gen-DataC : Tactic
--   gen-DataC hole = do
--     hLam (abs "ℓs" t@(def d args)) ← quoteωTC (λ {ℓs} → Nᶜ {ℓs})
--       where t → typeError (termErr t ∷ strErr " is not a definition." ∷ [])
--     data-type pars cs ← getDefinition d
--       where _ → typeError (nameErr d ∷ strErr " is not a data type." ∷ [])

--     `toN       ← gen-toN cs
--     `fromN     ← gen-fromN
--     `fromN-toN ← gen-fromN-toN
--     `toN-fromN ← gen-toN-fromN
    
--     checkedHole ← checkType hole =<< quoteTC (DataCᶜ D Nᶜ)
--     unify checkedHole $ `dataC `toN `fromN `fromN-toN `toN-fromN



