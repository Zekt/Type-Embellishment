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

  -- Generate the corresponding clause of a given constructor name
  conClause : (rec : Term) → ℕ → ℕ → Telescope → Name → TC Clause
  conClause rec pars #levels parCxt conName = do
    conCxt ← forgetTypes <$> getConTelescope conName pars
    
    let ℓs = `Levels #levels
    let  |conCxt|  = length conCxt ; |parCxt| = length parCxt
    let (_ , conArgs , pat₂) = cxtToVars 0 (`tt , `tt) conCxt 
        (_ , args , pat₁)    = cxtToVars |conCxt| (`tt , `tt) parCxt
    let (_ , _ , pat) = cxtToVars (|conCxt| + |parCxt|) (`tt , `tt) ℓs

    let term = rec `$$ args `$$ [ vArg (con conName $ hUnknowns pars <> conArgs) ]
    
    term ← runSpeculative $ extend*Context (parCxt <> conCxt) $ do
      (_, false) <$> normalise term
      -- normalise term
    -- levels that should be in the telescope of pattern
    let cxt = ℓs <> parCxt <> conCxt
        pat = pat <> pat₁ <> [ vArg (con conName pat₂) ]
    return $ cxt ⊢ pat `= term

defineFold : FoldP → Name → TC _
defineFold P f = do
  `P ← quoteωTC P
  pars , cs ← getDataDefinition =<< FoldPToNativeName P

  cls ← extendContextℓs #levels λ ℓs → do
    declareDef (vArg f) =<< prependLevels #levels <$> quoteTC! (FoldNT P ℓs)
    Γps  ← fromTel! (Param ℓs)
    let rec = def₂ `fold-base `P (def₀ f)
    forM cs $ conClause rec pars #levels Γps
  defineFun f cls
  where open FoldP P

defineInd : IndP → Name → TC _
defineInd P f = do
  `P ← quoteωTC P
  pars , cs ← getDataDefinition =<< IndPToNativeName P

  cls ← extendContextℓs #levels λ ℓs → do
    declareDef (vArg f) =<< prependLevels #levels <$> quoteTC! (IndNT P ℓs)
    Γps  ← fromTel! (Param ℓs)
    let rec = def₂ `ind-base `P (def₀ f)
    forM cs $ conClause rec pars #levels Γps
  defineFun f cls
  where open IndP P
