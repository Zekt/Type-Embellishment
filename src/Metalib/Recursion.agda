{-# OPTIONS --without-K #-}
open import Prelude

module Metalib.Recursion where

open import Utils.Reflection
open import Utils.Error as Err

open import Generics.Description as D
open import Generics.Recursion   as D

open import Metalib.Telescope

genFold : FoldP → Name → TC _
genFold P &fold = extendContextℓs #levels λ ℓs → do
  t' ← quoteTC (FoldNT P ℓs) >>= normalise
  let t = prependLevels t' #levels
  dprint [ strErr "Type of Fold:" ]
  dprint [ termErr $ t ]
  declareDef (vArg &fold) t
  -- Assuming that the last argument to fold is always the target datatype
  -- tel is without levels since levels of FoldP is uncurried but the native should be curried.
  let tel = fst $ ⇑ t'
  foldLast ← maybe′ (return ∘ unArg ∘ snd)
                    (Err.notEndIn (nameErr &fold) (strErr "datatype"))
                    (last tel)
  dprint [ strErr $ "Last argument to the generated fold function:" ]
  dprint [ strErr $ showTerm foldLast ]
  pars , conNames ← getDataDefinition =<< getTermName foldLast
  let tel' = fst $ splitAt (length tel ∸ 1) tel
  cxt ← getContext
  dprint [ strErr "Context before defining function clauses:" ]
  dprint [ strErr (showTel cxt) ]
  cls ← mapM (conClause pars tel') conNames
  defineFun &fold cls
  return tt
  where
    open FoldP P
    prependLevels : Type → ℕ → Type
    prependLevels t zero = t
    prependLevels t (suc n) = pi (hArg (quoteTerm Level))
                                 (abs "ℓ" $ prependLevels t n)

    getTermName : Term → TC Name
    getTermName (con c args) = return c
    getTermName (def f args) = return f
    getTermName t = Err.notApp t

    conClause : ℕ → Telescope → Name → TC Clause
    conClause pars cxt conName = do
      conType ← getType conName
      let conCxt = drop pars $ fst (⇑ conType)
      -- dummy function for application
      foldP  ← quoteωTC (fold-base P)
      foldPT ← inferType foldP >>= normalise
      &foldP ← freshName ""
      dprint [ termErr foldPT ]

      declareDef (vArg &foldP) foldPT
      defineFun &foldP [ [] ⊢ [] `= foldP ]
      foldBody ← extend*Context (cxt <> conCxt) $ do
                   let term = (def &foldP $ [ vArg (def₀ &fold) ]                          <>
                                            foldVars cxt (λ n → var₀ (n + length conCxt))  <>
                                            [ vArg (con conName (foldVars conCxt var₀)) ])
                   cxt ← getContext
                   dprint (strErr "Context before clause generation:" ∷ [ strErr $ showTel cxt ])
                   dprint [ strErr "Generated term of a clause:" ]
                   dprint [ strErr $ showTerm term ]
                   dprint [ termErr term ]
                   normalise term
      dprint [ strErr $ showTerm foldBody ]
      let cxt' = duplicate #levels ("ℓ" , (hArg (quoteTerm Level))) <> cxt
      dprint [ strErr $ showTel cxt' ]
      return $ (cxt' <> conCxt)
             ⊢ foldVars cxt' (λ n → var (n + length conCxt)) <> [ vArg (con conName (foldVars conCxt var)) ]
            `= foldBody
      where
        -- would be better if it's typeclass
        foldVars : ∀ {X : Set} → Telescope → (ℕ → X) → List (Arg X)
        foldVars [] _ = []
        foldVars ((s , arg i x) ∷ tel) f =
          arg i (f (length tel)) ∷ foldVars tel f
