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

private
  prependLevels : ℕ → Type → Type
  prependLevels n = prependToType (`Levels n)

  pattern `fold-base = quote fold-base
  pattern `ind-base  = quote ind-base

  -- Generate the corresponding clause of a given constructor name
  conClause : {A : Setω} (rec f : Name) (F : A) → (pars #levels : ℕ) → Telescope → Name → TC Clause
  conClause rec f F pars #levels Γps c = do
    `F ← quoteωTC F
    Γc ← forgetTypes <$> getConTelescope c pars

    let Γℓs = `Levels #levels
    let |Γc|  = length Γc ; |Γps| = length Γps
    let (_ , cArgs , cPats)    = cxtToVars 0              (`tt , `tt) Γc 
    let (_ , psArgs , psPats)  = cxtToVars |Γc|           (`tt , `tt) Γps
    let ((ℓt , _) , _ , ℓPats) = cxtToVars (|Γc| + |Γps|) (`tt , `tt) Γℓs
    
    return $ (Γℓs <> Γps <> Γc)
      ⊢ ℓPats <> psPats <> vArg (con c cPats) ∷ [] `=
        (def rec $ (vArg `F ∷ hArg ℓt ∷ vArg (def f []) ∷ []) <> psArgs <> [ vArg (con c $ hUnknowns pars <> cArgs) ])

defineFold : FoldP → Name → TC _
defineFold P f = do
  `type ← prependLevels #levels <$> exCxtℓs #levels λ ℓs → do
      ss ← fromTelInfo (ParamN {ℓs})
      T  ← quoteTC! (FoldNT P ℓs)
      return $ renameTypeBy T ss

  declareDef (vArg f) (unConflictType `type)

  pars , cs ← getDataDefinition =<< FoldPToNativeName P

  cls ← exCxtℓs #levels λ ℓs → do
    Γps ← fromTel (Param ℓs) ParamV
    ss  ← fromTelInfo (ParamN {ℓs})
    forM cs $ conClause `fold-base f P pars #levels (renameTelBy Γps ss)
  cls ← noConstraints $ normalise onClauses cls

  defineFun f cls
  printFunction false f
  where open FoldP P

defineInd : IndP → Name → TC _
defineInd P f = do
  `type ← prependLevels #levels <$> exCxtℓs #levels λ ℓs → do
    ss ← fromTelInfo (ParamN {ℓs})
    T  ← quoteTC! (IndNT P ℓs)
    return $ renameTypeBy T ss

  declareDef (vArg f) $ unConflictType `type

  pars , cs ← getDataDefinition =<< IndPToNativeName P

  cls ← exCxtℓs #levels λ ℓs → do
    Γps ← fromTel (Param ℓs) ParamV
    ss  ← fromTelInfo (ParamN {ℓs})
    forM cs $ conClause `ind-base f P pars #levels (renameTelBy Γps ss)

  cls ← noConstraints $ normalise onClauses cls
  defineFun f cls

  printFunction false f
  where open IndP P
