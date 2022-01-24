{-# OPTIONS --without-K --safe #-}
open import Prelude

module Generics.Reflection.Recursion where

open import Utils.Reflection
open import Utils.Error as Err

open import Generics.Telescope
open import Generics.Algebra
open import Generics.Description 
open import Generics.Recursion   

open import Generics.Reflection.Telescope
open import Generics.Reflection.Name

normaliseClause : Clause → TC Clause
normaliseClause (tel ⊢ ps `= t) = do
  printTelescope tel (return []) >>= dprint 
  u ← extend*Context tel (normalise t)
  return $ tel ⊢ ps `= u
normaliseClause cl = return cl

normaliseClauses : Clauses → TC Clauses
normaliseClauses = mapM normaliseClause

checkClauses : Clauses → Type → TC Clauses
checkClauses cls `A = do
  pat-lam₀ cls ← checkType (pat-lam₀ cls) `A
    where _ → IMPOSSIBLE
  return cls

private
  prependLevels : ℕ → Type → Type
  prependLevels n = prependToType (`Levels n)

  pattern `fold-base = quote fold-base
  pattern `ind-base  = quote ind-base

  -- Generate the corresponding clause of a given constructor name
  conClause : (rec : Term) → (pars #levels : ℕ) → Telescope → Name → TC Clause
  conClause rec pars #levels Γps c = do
    Γc ← forgetTypes <$> getConTelescope c pars
    
    let Γℓs = `Levels #levels
    let |Γc|  = length Γc ; |Γps| = length Γps
    let (_ , cArgs , cPats)   = cxtToVars 0              (`tt , `tt) Γc 
    let (_ , psArgs , psPats) = cxtToVars |Γc|           (`tt , `tt) Γps
    let (_ , _ , ℓs)          = cxtToVars (|Γc| + |Γps|) (`tt , `tt) Γℓs

    return $ (Γℓs <> Γps <> Γc)
      ⊢ ℓs <> psPats <> vArg (con c cPats) ∷ [] `=
        (rec `$$ psArgs `$$ [ vArg (con c $ hUnknowns pars <> cArgs) ])

defineFold : FoldP → Name → TC _
defineFold P f = do
  `P ← quoteωTC P
  `type ← prependLevels #levels <$> extendContextℓs #levels λ ℓs →
      quoteTC! (FoldNT P ℓs)
  declareDef (vArg f) `type

  let rec = def₂ `fold-base `P (def₀ f)
  pars , cs ← getDataDefinition =<< FoldPToNativeName P

  cls ← extendContextℓs #levels λ ℓs → do
    Γps  ← fromTel! (Param ℓs)
    forM cs $ conClause rec pars #levels Γps
  cls ← noConstraints $ normaliseClauses =<< checkClauses cls `type

  defineFun f cls
  printFunction false f
  where open FoldP P

defineInd : IndP → Name → TC _
defineInd P f = do
  `P ← quoteωTC P
  `type ← prependLevels #levels <$> extendContextℓs #levels λ ℓs →
    quoteTC! (IndNT P ℓs)
  declareDef (vArg f) `type

  let ind = def₂ `ind-base `P (def₀ f)
  pars , cs ← getDataDefinition =<< IndPToNativeName P

  cls ← extendContextℓs #levels λ ℓs → do
    Γps  ← fromTel! (Param ℓs)
    forM cs $ conClause ind pars #levels Γps

  cls ← noConstraints $ normaliseClauses =<< checkClauses cls `type
  
  defineFun f cls

  printFunction false f
  where open IndP P
