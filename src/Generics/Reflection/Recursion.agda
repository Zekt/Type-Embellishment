{-# OPTIONS --without-K --safe #-}
open import Prelude

module Generics.Reflection.Recursion where

open import Utils.Reflection
open import Utils.Error as Err

open import Generics.Description as D
open import Generics.Recursion   as D

open import Generics.Reflection.Telescope

private
  prependLevels : Type → ℕ → Type
  prependLevels t zero = t
  prependLevels t (suc n) = pi (hArg (quoteTerm Level))
                               (abs "ℓ" $ prependLevels t n)

  getTermName : Term → TC Name
  getTermName (con c args) = return c
  getTermName (def f args) = return f
  getTermName t = Err.notApp t

  -- generate variable terms that should refer to the given context,
  foldVars : ∀ {X : Set} → Telescope → (ℕ → X) → List (Arg X)
  foldVars [] _ = []
  foldVars ((s , arg i x) ∷ tel) f =
    arg i (f (length tel)) ∷ foldVars tel f

  -- Generate the corresponding clause of a given constructor name
  conClause : Name → Term → ℕ → ℕ → Telescope → Name → Name → TC Clause
  conClause &fun qP npars #levels parCxt base conName = do
    conType ← getType conName
    let preConCxt = fst (⇑ conType)
        conCxt    = drop npars preConCxt
        conCxt'   = map (λ (s , A) → (s , arg (getArgInfo A) unknown)) conCxt
        conArgs   = foldVars conCxt var₀
        args      = foldVars parCxt (λ n → var₀ (n + length conCxt))
        -- dprint [ strErr "Given argumets to base:" ]
        -- dprint [ strErr $ showTerms args ]
    term ← extend*Context (parCxt <> conCxt') $ do
             let term = (def base $
                              [ vArg qP ]
                           <> [ vArg (def₀ &fun) ]
                           <> args
                           <> [ vArg (con conName (hUnknowns npars <> conArgs)) ])
             normalise term
    -- levels that should be in the telescope of pattern
    let ℓparCxt = duplicate #levels ("ℓ" , (hArg (quoteTerm Level))) <> parCxt
        cxt = ℓparCxt <> conCxt'
        pat = foldVars ℓparCxt (λ n → var (n + length conCxt')) <>
              [ vArg (con conName (foldVars conCxt' var)) ]
    return $ cxt ⊢ pat `= term

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

  parTel ← withNormalisation true $ fromTel (Param ℓs)
  -- dprint [ strErr $ "Parameter telecsope: " ]
  -- dprint [ strErr $ showTel parTel ]
  -- npars is the number of parameters including levels
  npars , conNames ← getDataDefinition =<< (getTermName foldLast)
  qP ← quoteωTC P
  cls ← mapM (conClause &fold qP npars #levels parTel (quote fold-base)) conNames
  defineFun &fold cls
  where
    open FoldP P

defineInd : IndP → Name → TC _
defineInd P &ind = extendContextℓs #levels λ ℓs → do
  indT' ← quoteTC! (IndNT P ℓs)
  let indT = prependLevels indT' #levels
  declareDef (vArg &ind) indT
  indLast ← case (last ∘ fst $ ⇑ indT) of λ where
              (just x) → return ∘ unArg ∘ snd $ x
              nothing  → Err.notEndIn (nameErr &ind) (strErr "datatype")
  parTel ← withNormalisation true $ fromTel (Param ℓs)
  npars , conNames ← getDataDefinition =<< (getTermName indLast)
  qP ← quoteωTC P
  cls ← mapM (conClause &ind qP npars #levels parTel (quote ind-base)) conNames
  defineFun &ind cls
  where
    open IndP P
