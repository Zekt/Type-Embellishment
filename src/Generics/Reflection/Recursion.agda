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

removeAbsurdClauses : Clauses → Clauses
removeAbsurdClauses []                        = []
removeAbsurdClauses (cl@(clause _ _ _) ∷ cls) = cl ∷ removeAbsurdClauses cls
removeAbsurdClauses (absurd-clause _ _ ∷ cls) = removeAbsurdClauses cls 

dontReduce⦂ : {A : Set ℓ}
  → TC A → TC A
dontReduce⦂ = dontReduceDefs [ quote idFun ]

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
  `type ← dontReduce⦂ $ prependLevels #levels <$> extendContextℓs #levels λ ℓs →
      quoteTC! (FoldNT P ℓs)
  declareDef (vArg f) `type

  let rec = def₂ `fold-base `P (def₀ f)
  pars , cs ← getDataDefinition =<< FoldPToNativeName P

  cls ← extendContextℓs #levels λ ℓs → do
    Γps  ← fromTel! (Param ℓs)
    forM cs $ conClause rec pars #levels Γps
  cls ← noConstraints $ (reduce onClauses_) =<< checkClauses cls `type

  defineFun f cls
  printFunction false f
  where open FoldP P

defineInd : IndP → Name → TC _
defineInd P f = do
  `P ← quoteωTC P
  `type ← dontReduce⦂ $ prependLevels #levels <$> extendContextℓs #levels λ ℓs →
    quoteTC! (IndNT P ℓs)
  declareDef (vArg f) `type

  let ind = def₂ `ind-base `P (def₀ f)
  pars , cs ← getDataDefinition =<< IndPToNativeName P

  cls ← extendContextℓs #levels λ ℓs → do
    Γps  ← fromTel! (Param ℓs)
    forM cs $ conClause ind pars #levels Γps

  cls ← noConstraints $ (reduce onClauses_) =<< checkClauses cls `type
  
  defineFun f cls

  printFunction false f
  where open IndP P
