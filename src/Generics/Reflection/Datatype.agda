{-# OPTIONS --safe --without-K #-}

open import Prelude

module Generics.Reflection.Datatype where
open import Utils.Reflection
open import Utils.Error          as Err

open import Generics.Telescope
open import Generics.Description 
open import Generics.Reflection.Telescope
open import Generics.Reflection.Constructor

private
  variable
    rb  : RecB
    cb  : ConB
    cbs : ConBs
    t u : Tel ℓ

private
  pattern `datad x y        = con₂ (quote datad) x y
  pattern `pdatad x y z u v = con (quote pdatad)
    (vArg x ∷ iArg y ∷ vArg z ∷ vArg u ∷ vArg v ∷ [])
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
  map (prefixToType `Param) <$>
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
  let `Levels = levels #levels
  let Dᵖ      = applyL ℓs
  `Param , dT ← withNormalisation true $ getSignature Dᵖ
  -- dprint (strErr "`Param:\n" ∷ strErr (show `Param) ∷ [])
  -- dprint (strErr "Type:\n" ∷ termErr dT ∷ [])
  declareData dataN (#levels + length `Param) (prefixToType `Levels dT)

  conTs ← withNormalisation true $ map (prefixToType `Levels) <$> getCons dataN `Param Dᵖ
  defineData dataN (zip conNs conTs)
  where open DataD dataD

------------------------------------------------------------------------
-- Translate an meta-level datatype declaration to the its object-level
-- description

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
    -- Indices in recursion in Description is different from those in native constructors! Should strengthen by one instead of abstracting.
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

reifyData : Name → TC Term
reifyData d = do
    dataType ← getType d
    pars , cs ← getDataDefinition d

    -- Assumption: the type of a datatype consists of
    --   ℓs : a telescope of Levels
    --   Γ  : a telescope of parameter types
    --   Δ  : a telescope of index types
    let (ℓsΓΔ , end) = (⇑ dataType) ⦂ Telescope × Type
        (ℓsΓ  , Δ)   = splitAt pars ℓsΓΔ
        (ℓtel , Γ)   = span (λ (_ , `A) → unArg `A == `Level) ℓsΓ
        lenΓΔ        = length Γ + length Δ
        strengthenByΓΔ = strengthen lenΓΔ lenΓΔ

    let `#levels     = lit (nat (length ℓtel))

    `ℓ      ← getSetLevel end
    conDs ← to`ConDs <$> mapM (reifyConstructor d pars) cs

    return $ `datad `#levels
      (patLam ℓtel
        (`pdatad (strengthenByΓΔ `ℓ) `refl (strengthenByΓΔ $ to`Tel Γ)
          (patLam Γ $ to`Tel Δ)
          (patLam Γ conDs)))
  where
    patLam : Telescope → Term → Term
    patLam Γ body = let (_ , p) , _ = cxtToVars (`tt , `tt) Γ in
      pat-lam₀ [ Γ ⊢ [ vArg p ] `= body ]
      
macro
  genDataD : Name → Tactic
  genDataD d hole = do
    checkedHole ← checkType hole (quoteTerm DataD) 
    unify checkedHole =<< reifyData d
