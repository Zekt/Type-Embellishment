{-# OPTIONS --safe --without-K #-}
open import Prelude

module Metalib.Connection where

open import Utils.Reflection
open import Utils.Error as Err

open import Generics.Description
open import Generics.Recursion  

private
  pattern `inl x   = con₁ (quote _⊎_.inl) x
  pattern `inr x   = con₁ (quote _⊎_.inr) x
  pattern `refl    = con₀ (quote _≡_.refl)
  pattern _`,_ x y = con₂ (quote Prelude._,_) x y

------------------------------------------------------------------------
-- Each constructor `c : (x₁ : A₁) → (x₂ : A₂ x₁) → ⋯ → T`
-- can be represented as a pattern on the LHS `c x₁ x₂ ⋯ xₙ` or as a term on the RHS
-- They can be also uncurried described by ⟦ ConD ⟧. Thus, there are 4 types of constructor representations. 
cxtToVars : (Γ : Telescope) → (Term × Pattern) × (Args Term × Args Pattern)
cxtToVars = snd ∘ foldr emptyVar λ where
      (_ , arg i _) (n , (t , p) , (targs , pargs)) →
        suc n , ((var₀ n `, t) , (var n `, p)) , (arg i (var₀ n) ∷ targs) , (arg i (var n) ∷ pargs)
  where emptyVar = 0 , (`refl , `refl) , ([] , [])

forgetTy : Telescope → Telescope
forgetTy = map $ bimap id (λ `A → arg (getArgInfo `A) unknown)

module _ (pars : ℕ) where
  conToClause : (c : Name) → TC (Telescope × (Term × Pattern) × Args Term × Args Pattern)
  conToClause c = do
    `A  ← getType c
    tel ← drop pars <$> (renameUnderscore $ (⇑ `A) .fst)
    return $ < forgetTy , cxtToVars > tel

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
  
genDataCT : (D : DataD) → (Nᶜ : DataTᶜ D) → Tactic
genDataCT D Nᶜ hole = do
  `D ← quoteωTC D
  `N ← quoteωTC {A = ∀ {ℓs} → PDataTᶜ (DataD.applyL D ℓs)} Nᶜ
  hole ← checkType hole (def₂ (quote DataCᶜ) `D `N)
  
  hLam (abs "ℓs" t@(def d args)) ← quoteωTC (λ {ℓs} → Nᶜ {ℓs})
    where t → Err.notDef t
  pars , cs ← getDataDefinition d

  `toN       ← genToNT       pars cs
  `fromN     ← genFromNT     pars cs 
  `fromN-toN ← genFromN-toNT pars cs 
  `toN-fromN ← genToN-fromNT pars cs 

  unify hole $ con₄ (quote datac) `toN `fromN `fromN-toN `toN-fromN

private
  fromData : (f : ℕ → Names → TC Term) → Name → Tactic
  fromData f d hole = getDataDefinition d >>= uncurry f >>= unify hole

macro
  genToN       = fromData genToNT
  genFromN-toN = fromData genFromN-toNT
  genFromN     = fromData genFromNT
  genToN-fromN = fromData genToN-fromNT

  genDataC : (D : DataD) → (Nᶜ : DataTᶜ D) → Tactic
  genDataC = genDataCT
