{-# OPTIONS --without-K #-}

open import Prelude

module Metalib.Datatype where

open import Utils.Reflection
open import Utils.Error          as Err

open import Generics.Telescope   as Desc
open import Generics.Description as Desc
open import Generics.Levels      as Desc

open import Metalib.Telescope as Tel

--
argVars : ℕ → (weakenBy : ℕ) → Args Term
argVars zero    wk = []
argVars (suc N) wk = vArg (var₀ (N + wk)) ∷ argVars N wk

-- Translate the semantics of an object-level telescope to
-- a context
idxToArgs : {T : Tel ℓ} → ⟦ T ⟧ᵗ → TC Context
idxToArgs {T = []}    tt        = return []
idxToArgs {T = _ ∷ _} (x , ⟦T⟧) = do
  `T ← idxToArgs ⟦T⟧
  `x ← quoteTC x
  return (vArg `x ∷ `T)

private variable
  rb  : RecB
  cb  : ConB
  cbs : ConBs

module _ (d : Name) (pars : ℕ) {T : Tel ℓ} where
  unknowns : Args Term
  unknowns = duplicate pars (vArg unknown)

  RecDToType : (R : RecD ⟦ T ⟧ᵗ rb) → TC Type
  RecDToType (ι i) = do
    idxs ← idxToArgs i
    return $ def d (unknowns <> idxs)
  RecDToType (π A D) = extendContextT visible-relevant-ω A λ `A x →
      vΠ[ `A ]_ <$> RecDToType (D x)

  ConDToType : (D : ConD ⟦ T ⟧ᵗ cb) → TC Type
  ConDToType (ι i) = do
    idxs ← idxToArgs i
    return $ def d (unknowns <> idxs)
  ConDToType (σ A D) = extendContextT visible-relevant-ω A λ `A x →
    vΠ[ `A ]_ <$>  ConDToType (D x)
  ConDToType (ρ R D) = do
    `R ← RecDToType R
    extendContext (vArg (quoteTerm ⊤)) do
    -- we might still need to give a correct type
      vΠ[ `R ]_ <$> ConDToType D

  ConDsToTypes : (Ds : ConDs ⟦ T ⟧ᵗ cbs) → TC (List Type)
  ConDsToTypes []       = return []
  ConDsToTypes (D ∷ Ds) = ⦇ ConDToType D ∷ ConDsToTypes Ds ⦈

getCons : Name → (pars : ℕ) → (`Param : Telescope) → PDataD → TC (List Type)
getCons d pars `Param Dᵖ = extendContextTs (PDataD.Param Dᵖ) λ ⟦Ps⟧ →
  map (prefixToType `Param) <$> ConDsToTypes d pars (PDataD.applyP Dᵖ ⟦Ps⟧)
{-# INLINE getCons #-}

getSignature : PDataD → TC (ℕ × Type × Telescope)
getSignature Dᵖ = let open PDataD Dᵖ in do
  pars  , `Param ← fromTel Param
  dT             ← fromTelType (Param Desc.++ Index) (Set dlevel)
  return $ pars , dT , `Param

defineByPDataD : Name → PDataD → TC (ℕ × Type × List Type)
defineByPDataD dataN dataD = do
  pars , `Param ← fromTel Param
  dataT         ← fromTelType (Param Desc.++ Index) (Set dlevel)
  extendContextTs Param λ ⟦Ps⟧ → do
    conTs ← map (prefixToType `Param)
      <$> ConDsToTypes dataN pars (applyP ⟦Ps⟧)
    return $ pars , dataT , conTs
  where open PDataD dataD

defineByDataD : DataD → Name → List Name → TC _
defineByDataD dataD dataN conNs = extendContextℓs #levels λ ℓs → do
  pars , dataT , conTs ← defineByPDataD dataN $ applyL ℓs
  -- dataT and conTs do not contain Level in their types
  let `Levels = levels #levels
  let Dᵖ      = applyL ℓs
  pars , dT , `Param ← getSignature Dᵖ
  declareData dataN (#levels + pars) (prefixToType `Levels dT)

  conTs ← map (prefixToType `Levels) <$> getCons dataN pars `Param Dᵖ
  defineData dataN (zip conNs conTs)
  where open DataD dataD

---------
argsToIdx : List (Arg Type) → Term
argsToIdx []       = quoteTerm tt
argsToIdx (x ∷ xs) = con (quote _,_)
                         (x ∷ vArg (argsToIdx xs) ∷ [])

endsIn : Type → Name → Bool
endsIn (pi a (abs _ b)) u = endsIn b u
endsIn (def f args)     u = f == u
endsIn t                u = false

module _ (dataName : Name) (#levels : ℕ) (parLen : ℕ) where
  telescopeToRecD : Telescope → Type → TC Term
  telescopeToRecD ((s , arg _ `x) ∷ `tel) end = do
    rec ← telescopeToRecD `tel end
    return (con (quote RecD.π) (vArg `x ∷ vArg (vLam (abs s rec)) ∷ []))

  telescopeToRecD [] (def f args) with f == dataName
  ... | true  = return (con (quote RecD.ι)
                            [ vArg $ argsToIdx $ drop (#levels + parLen) args ])
  ... | false = Err.notEndIn dataName

  telescopeToRecD [] _ = Err.notEndIn dataName


  telescopeToConD : Telescope → Type → TC Term
  telescopeToConD ((s , (arg _ `x)) ∷ `tel) end with endsIn `x dataName
  ... | true = do
    recd ← uncurry telescopeToRecD (⇑ `x)
    cond ← telescopeToConD `tel end
    return (con (quote ρ) (vArg recd ∷ vArg cond ∷ []))
  ... | false = do
    cond ← telescopeToConD `tel end
    return (con (quote σ) (vArg `x ∷ vArg (vLam (abs s cond)) ∷ []))

  telescopeToConD [] (def f args) with f == dataName
  ... | true  = return $ con (quote ConD.ι)
                             [ vArg $ argsToIdx $ drop (#levels + parLen) args ]
  ... | false = Err.notEndIn dataName

  telescopeToConD [] _ = Err.notEndIn dataName

  describeConstructor : Name → TC Term
  describeConstructor conName = do
    conType ← getType conName
    let (tel , end) = ⇑_ ⦃ TypeToTelescope ⦄ conType
    let tel' = drop (#levels + parLen) tel
    telescopeToConD tel' end


describeData : ℕ → Name → List Name → TC Term
describeData parLen dataName conNames = do
    dataType ← getType dataName
    let (tel     , end) = ⇑_ ⦃ TypeToTelescope ⦄ dataType
        (#levels , tel) = splitLevels tel
        (par     , idx) = splitAcc [] tel parLen
    conDefs ← mapM (describeConstructor dataName #levels parLen) conNames
    level  ← getTypeLevel end
    `level ← quoteTC level
    `refl  ← quoteTC {A = _≡_ {lzero} {Level} level level} _≡_.refl
    let applyBody : Term
        applyBody = foldr (con (quote ConDs.[]) [])
                          (λ x xs →
                            con (quote ConDs._∷_)
                                (vArg x ∷ vArg xs ∷ []))
                          conDefs
        `pdatad : Term
        `pdatad = con (quote pdatad)
                      (map vArg
                      (`level                  --level
                      ∷ `refl                  --level-pre-fixed-point
                      ∷ to`Tel par             --Param
                      ∷ patLam par (to`Tel idx)--Index
                      ∷ patLam par applyBody   --applyP
                      ∷ []))
    return `pdatad
  where
    splitLevels : Telescope → (ℕ × Telescope)
    splitLevels [] = 0 , []
    splitLevels t@((_ , arg _ a) ∷ tel) =
      if a == quoteTerm Level then bimap suc id (splitLevels tel)
                              else 0 , t

    splitAcc : Telescope → Telescope → ℕ → (Telescope × Telescope)
    splitAcc tel₁ []   n = tel₁ , []
    splitAcc tel₁ tel₂ 0 = tel₁ , tel₂
    splitAcc tel₁ (x ∷ tel₂) (suc n) = splitAcc (tel₁ <> [ x ]) tel₂ n
    to`Tel : Telescope → Term
    to`Tel []              = quoteTerm Tel.[]
    to`Tel ((s , x) ∷ tel) = con (quote Tel._∷_)
                                 (x
                                 ∷ vArg (vLam (abs s (to`Tel tel)))
                                 ∷ [])

    Σpat : Telescope → Arg Pattern
    Σpat [] = vArg (con (quote tt) [])
    Σpat ((s , arg _ x) ∷ tel) =
      vArg (con (quote _,_)
                (vArg (var (length tel)) ∷ Σpat tel ∷ []))

    patLam : Telescope → Term → Term
    patLam tel body = pat-lam [ clause tel [ Σpat tel ] body ] []
