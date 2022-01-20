{-# OPTIONS --safe --without-K #-}

open import Prelude

module Generics.Reflection.Datatype where
open import Utils.Reflection
open import Utils.Error          as Err

open import Generics.Telescope
open import Generics.Description 
open import Generics.Reflection.Telescope

private
  variable
    rb  : RecB
    cb  : ConB
    cbs : ConBs
    t u : Tel ℓ

  pattern `[]      = con₀ (quote ConDs.[])
  pattern _`∷_ x y = con₂ (quote ConDs._∷_) x y
  pattern `ιʳ  x   = con₁ (quote RecD.ι)    x
  pattern `π   x y = con₂ (quote RecD.π)    x y
  pattern `ιᶜ  x   = con₁ (quote ConD.ι)    x
  pattern `σ   x y = con₂ (quote ConD.σ)    x y
  pattern `ρ   x y = con₂ (quote ConD.ρ)    x y

to`ConDs : Terms → Term
to`ConDs = foldr `[] _`∷_
------------------------------------------------------------------------
-- Translate an object-level datatype description `DataD` to the meta-level
-- declaration 
module _ {T : Tel ℓ} (`A : ⟦ T ⟧ᵗ → TC Type) where
  RecDToType : (R : RecD ⟦ T ⟧ᵗ rb) → TC Type
  RecDToType (ι i) = `A i
  RecDToType (π A D) = do
    s ← getAbsNameω D
    extendContextT s visible-relevant-ω A λ `A x →
      vΠ[ s ∶ `A ]_ <$> RecDToType (D x)
      
  ConDToType : (D : ConD ⟦ T ⟧ᵗ cb) → TC Type
  ConDToType (ι i) = `A i
  ConDToType (σ A D) = do
    s ← getAbsNameω D
    extendContextT s visible-relevant-ω A λ `A x →
      vΠ[ s ∶ `A ]_ <$>  ConDToType (D x)
  ConDToType (ρ R D) = do
    `R ← RecDToType R
    extendContext "_" (vArg (quoteTerm ⊤)) do
      vΠ[ `R ]_ <$> ConDToType D
  ConDsToTypes : (Ds : ConDs ⟦ T ⟧ᵗ cbs) → TC (List Type)
  ConDsToTypes []       = return []
  ConDsToTypes (D ∷ Ds) = ⦇ ConDToType D ∷ ConDsToTypes Ds ⦈

getCons : Name → (`Param : Telescope) → PDataD → TC (List Type)
getCons d `Param Dᵖ = extendCxtTel Param λ ps →
  map (prependToType `Param) <$>
      ConDsToTypes (typeOfData d ps) (applyP ps)
  where open PDataD Dᵖ
{-# INLINE getCons #-}

getSignature : PDataD → TC (Telescope × Type)
getSignature Dᵖ = do
  `Param       ← fromTel Param
  `Param+Index ← fromTel (Param ++ Index)
  dT ← extend*Context `Param+Index do
    `Setℓ ← quoteTC! (Set dlevel)
    return $ ⇑ (`Param+Index , `Setℓ) ⦂ Type

  return $ `Param , dT
  where open PDataD Dᵖ

defineByDataD : DataD → Name → List Name → TC _
defineByDataD dataD dataN conNs = extendContextℓs #levels λ ℓs → do
  let `Levels = `Levels #levels
  let Dᵖ      = applyL ℓs
  `Param , dT ← withNormalisation true $ getSignature Dᵖ
  -- dprint (strErr "`Param:\n" ∷ strErr (show `Param) ∷ [])
  -- dprint (strErr "Type:\n" ∷ termErr dT ∷ [])
  declareData dataN (#levels + length `Param) (prependToType `Levels dT)

  conTs ← withNormalisation true $ map (prependToType `Levels) <$> getCons dataN `Param Dᵖ
  defineData dataN (zip conNs conTs)
  where open DataD dataD

printByDataD' : DataD → String → List String → TC String
printByDataD' dataD dataN conNs = extendContextℓs #levels λ ℓs → do
  let `Levels = levels #levels
  let Dᵖ      = applyL ℓs
  `Param , dT ← withNormalisation true $ getSignature Dᵖ
  let dataT   = (prefixToType `Levels dT)
      npars   = (#levels + length `Param)
  dName ← freshName dataN
  -- dprint (strErr "`Param:\n" ∷ strErr (show `Param) ∷ [])
  -- dprint (strErr "Type:\n" ∷ termErr dT ∷ [])
  conTs ← withNormalisation true $ map (prefixToType `Levels) <$> getCons dName `Param Dᵖ
  mapM (λ T → dprint (strErr (show T) ∷ [])) conTs
  printDataAs (dataN , dataT , npars) (alignZip 0 conNs conTs)
  where
    open DataD dataD
    alignZip : ∀ {B : Set} → ℕ → List String → List B → List (String × B)
    alignZip n xs [] = []
    alignZip n [] (x ∷ ys) = ("con" <> show n , x) ∷ alignZip (suc n) [] ys
    alignZip n (x ∷ xs) (y ∷ ys) = (x , y) ∷ alignZip n xs ys

------------------------------------------------------------------------
-- Reification of datatypes

private
  pattern `datad  x y     = con₂ (quote datad)  x y
  pattern `pdatad x z u v = con₄ (quote pdatad) x z u v

module _ (dataName : Name) (pars : ℕ) where
  idxArgs = argsToIdx ∘ drop pars

  telescopeToRecD : Telescope → Type → TC Term
  telescopeToRecD ((s , arg _ `x) ∷ `tel) end = do
    rec ← telescopeToRecD `tel end
    return $ `π `x (`vλ s `→ rec)
  telescopeToRecD [] (def f args) = if f == dataName
    then return $ `ιʳ (idxArgs args)
    else Err.notEndIn (strErr "telescope") (nameErr dataName)
  telescopeToRecD [] _ = Err.notEndIn (strErr "telescope") $ nameErr dataName

  telescopeToConD : Telescope → Type → TC Term
  telescopeToConD ((s , arg _ `x) ∷ `tel) end = if endsIn `x dataName
    then (do
      recd ← uncurry telescopeToRecD (⇑ `x)
      cond ← telescopeToConD `tel end
      -- Indices in recursion in Description is different from those in native constructors!
      -- Strengthen by one instead of abstracting.
      return $ `ρ recd (strengthen 0 1 cond)
    ) else (do
      cond ← telescopeToConD `tel end
      return $ `σ `x  (vLam (abs s cond))
    )
  telescopeToConD [] (def f args) = if f == dataName
    then (return $ `ιᶜ (idxArgs args))
    else (Err.notEndIn (strErr "telescope")  (nameErr dataName))
  telescopeToConD [] _ = Err.notEndIn (strErr "telescope") (nameErr dataName)

  reifyConstructor : Name → TC Term
  reifyConstructor conName = do
    conType ← getType conName
    let (tel , end) = (⇑ conType) ⦂ Telescope × Type
    telescopeToConD (drop pars tel) end

------------------------------------------------------------------------
-- `reifyData` takes a name and generates a term of `DataD`
-- Assumption: the type of a datatype consists of
--   ℓs : a telescope of Levels
--   Γ  : a telescope of parameter types
--   Δ  : a telescope of index types
reifyData : Name → TC Term
reifyData d = do
  (ℓsΓΔ , end) ← coerce'_to (Telescope × Type) <$> getType d
  pars , cs    ← getDataDefinition d

  let (ℓsΓ  , Δ) = splitAt pars ℓsΓΔ
      (ℓtel , Γ) = span (λ (_ , `A) → unArg `A == `Level) ℓsΓ
      `#levels   = lit (nat (length ℓtel))

  `ℓ    ← getSetLevel end
  conDs ← to`ConDs <$> mapM (reifyConstructor d pars) cs

  return $ `datad `#levels
    (patLam ℓtel
      (`pdatad
        -- [FIX] Check if `ℓ depends on parameters other than Level
        (strengthen 0 (length Γ + length Δ) `ℓ)
        (to`Tel Γ)
        (patLam Γ $ to`Tel Δ)
        (patLam Γ conDs)))
  where
    patLam : Telescope → Term → Term
    patLam Γ body = let (_ , p) , _ = cxtToVars 0 (`tt , `tt) Γ in
      pat-lam₀ [ Γ ⊢ [ vArg p ] `= body ]

macro
  genDataD : Name → Tactic
  genDataD d hole = do
    checkedHole ← checkType hole (quoteTerm DataD)
    unify checkedHole =<< reifyData d

-- Currently unusable because module names are always printed.
macro
  defineAndPrintData : DataD → String → List String → Tactic
  defineAndPrintData D s cs hole = do
    dName ← freshName s
    len ← extendContextℓs #levels λ ℓs → do
            return $ length $ PDataD.struct (applyL ℓs)
    conNames ← align len cs
    defineByDataD D dName conNames
    printData dName
    where
      open DataD D
      align : ℕ → List String → TC (List Name)
      align zero cs = return []
      align (suc n) [] = do c ← freshName "con"
      -- freshName does not generate new names when called repetitively
      -- because it does not modify scope.
                            ns ← align n []
                            return $ c ∷ ns
      align (suc n) (x ∷ cs) = ⦇ freshName x ∷ align n cs ⦈

-- Currently unusable due to Agda's scope checking.
macro
  printByDataD : DataD → String → List String → Tactic
  printByDataD D s cs hole = do s ← printByDataD' D s cs
                                dprint [ strErr s ]
