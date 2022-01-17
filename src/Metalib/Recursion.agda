{-# OPTIONS --without-K --safe #-}
open import Prelude

module Metalib.Recursion where

open import Utils.Reflection

open import Utils.Error as Err

open import Generics.Description as D
open import Generics.Recursion   as D

open import Metalib.Telescope

defineFold : FoldP → Name → TC _
defineFold P &fold = extendContextℓs #levels λ ℓs → do
  foldT' ← quoteTC! (FoldNT P ℓs)
  let foldT = prependLevels foldT' #levels
  -- dprint [ strErr "Type of Fold:" ]
  -- dprint [ termErr $ foldT ]
  declareDef (vArg &fold) foldT
  -- Assuming that the last parameter of fold is always the target datatype
  foldLast ← case (last ∘ fst $ ⇑ foldT) of λ where
               (just x) → return ∘ unArg ∘ snd $ x
               nothing  → Err.notEndIn (nameErr &fold) (strErr "datatype")

  -- dprint [ strErr $ "Last argument to the generated fold function:" ]
  -- dprint [ strErr $ showTerm foldLast ]
  parTel ← withNormalisation true $ fromTel (Param ℓs)
  -- dprint [ strErr $ "Parameter telecsope: " ]
  -- dprint [ strErr $ "length: " <> show (length parTel) ]
  -- dprint [ strErr $ showTel parTel ]
  -- npars already include number of levels
  npars , conNames ← getDataDefinition =<< (getTermName foldLast)
  cls ← mapM (conClause npars ℓs parTel) conNames
  defineFun &fold cls
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

    -- Generate the corresponding clause of a given constructor name
    conClause : ℕ → Levels → Telescope → Name → TC Clause
    conClause npars ℓs parCxt conName = do
      qP ← quoteωTC P
      conType ← getType conName
      let preConCxt = fst (⇑ conType)
          conCxt = drop npars preConCxt
          conCxt' = map (λ (s , A) → (s , arg (getArgInfo A) unknown)) conCxt
          conArgs = foldVars conCxt var₀
          args = foldVars parCxt (λ n → var₀ (n + length conCxt))
      -- dprint [ strErr "Given argumets to fold-base:" ]
      -- dprint [ strErr $ showTerms args ]
      -- dprint [ strErr $ "Current context:" ]
      cxt ← getContext
      -- dprint [ strErr $ show cxt ]
      -- dprint [ strErr "Context to be extended with:" ]
      -- dprint [ strErr $ showTel $ parCxt <> conCxt' ]
      foldBody ← extend*Context (parCxt <> conCxt') $ do
                  let term = (def (quote fold-base) $
                                   [ vArg qP ]
                                <> [ vArg (def₀ &fold) ]
                                <> args
                                <> [ vArg (con conName (hUnknowns npars <> conArgs)) ])
                  -- dprint [ strErr "Generated term of a clause:" ]
                  -- dprint [ strErr $ showTerm term ]
                  normalise term
      -- dprint [ strErr $ showTerm foldBody ]
      -- levels that should be in the telescope of pattern
      let ℓparCxt = duplicate #levels ("ℓ" , (hArg (quoteTerm Level))) <> parCxt
          cxt = ℓparCxt <> conCxt'
          pat = foldVars ℓparCxt (λ n → var (n + length conCxt')) <>
                [ vArg (con conName (foldVars conCxt' var)) ]
      return $ cxt ⊢ pat `= foldBody
      where
        -- generate variable terms that should refer to the given context,
        -- would be better if there's a typeclass
        foldVars : ∀ {X : Set} → Telescope → (ℕ → X) → List (Arg X)
        foldVars [] _ = []
        foldVars ((s , arg i x) ∷ tel) f =
          arg i (f (length tel)) ∷ foldVars tel f
