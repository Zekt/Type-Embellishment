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

private
  prependLevels : ℕ → Type → Type
  prependLevels n = prependToType (`Levels n)

  pattern `fold-base = quote fold-base
  pattern `ind-base  = quote ind-base

FoldPToNativeName : FoldP → TC Name
FoldPToNativeName P = do
  extendContextℓs (DataD.#levels Desc) λ ℓs →
    extendCxtTel (PDataD.Param (DataD.applyL Desc ℓs)) λ ps → 
      extendCxtTel (PDataD.Index (DataD.applyL Desc ℓs) ps) λ is → do
        (def d _) ← quoteTC! $ Native ℓs ps is
          where t → IMPOSSIBLE
        return d
  where open FoldP P

IndPToNativeName : IndP → TC Name
IndPToNativeName P = do
  extendContextℓs (DataD.#levels Desc) λ ℓs →
    extendCxtTel (PDataD.Param (DataD.applyL Desc ℓs)) λ ps → 
      extendCxtTel (PDataD.Index (DataD.applyL Desc ℓs) ps) λ is → do
        (def d _) ← quoteTC! $ Native ℓs ps is
          where t → IMPOSSIBLE
        return d
  where open IndP P

private
  -- Generate the corresponding clause of a given constructor name
  conClause : (rec : Term) → (pars #levels : ℕ) → Telescope → Name → TC Clause
  conClause rec pars #levels Γps c = do
    Γc ← forgetTypes <$> getConTelescope c pars
    
    let Γℓs = `Levels #levels
    let |Γc|  = length Γc ; |Γps| = length Γps
    let (_ , cArgs , cPats)   = cxtToVars 0              (`tt , `tt) Γc 
    let (_ , psArgs , psPats) = cxtToVars |Γc|           (`tt , `tt) Γps
    let (_ , _ , ℓs)          = cxtToVars (|Γc| + |Γps|) (`tt , `tt) Γℓs

    term ← runSpeculative $ extend*Context (Γps <> Γc) $ do
      (_, false) <$> normalise
        (rec `$$ psArgs `$$ [ vArg (con c $ hUnknowns pars <> cArgs) ])

    return $ (Γℓs <> Γps <> Γc)
      ⊢ ℓs <> psPats <> vArg (con c cPats) ∷ [] `= term

defineFold : FoldP → Name → TC _
defineFold P f = do
  `P ← quoteωTC P
  let rec = def₂ `fold-base `P (def₀ f)

  pars , cs ← getDataDefinition =<< FoldPToNativeName P

  declareDef (vArg f) =<<
    prependLevels #levels <$> extendContextℓs #levels λ ℓs → quoteTC! (FoldNT P ℓs)

  defineFun f =<< 
    extendContextℓs #levels λ ℓs → do
      Γps  ← fromTel! (Param ℓs)
      forM cs $ conClause rec pars #levels Γps

  printFunction f
  where open FoldP P

defineInd : IndP → Name → TC _
defineInd P f = do
  `P ← quoteωTC P
  let ind = def₂ `ind-base `P (def₀ f)

  pars , cs ← getDataDefinition =<< IndPToNativeName P

  declareDef (vArg f) =<<
    prependLevels #levels <$> extendContextℓs #levels λ ℓs → quoteTC! (IndNT P ℓs)

  defineFun f =<<
    extendContextℓs #levels λ ℓs → do
      Γps  ← fromTel! (Param ℓs)
      forM cs $ conClause ind pars #levels Γps

  printFunction f
  where open IndP P
