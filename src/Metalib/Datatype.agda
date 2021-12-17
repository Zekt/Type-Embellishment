{-# OPTIONS --without-K #-}

open import Prelude
  hiding (_++_)

module Metalib.Datatype where

open import Prelude.List as L
open import Utils.Reflection

open import Generics.Telescope   as Desc
open import Generics.Description as Desc

open import Metalib.Telescope as Tel

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
    return $ def d (unknowns L.++ idxs)
  RecDToType (π A D) = extendContextT visible-relevant-ω A λ `A x →
      vΠ[ `A ]_ <$> RecDToType (D x)

  ConDToType : (D : ConD ⟦ T ⟧ᵗ cb) → TC Type
  ConDToType (ι i) = do
    idxs ← idxToArgs i
    return $ def d (unknowns L.++ idxs)
  ConDToType (σ A D) = extendContextT visible-relevant-ω A λ `A x →
    vΠ[ `A ]_ <$>  ConDToType (D x)
  ConDToType (ρ R D) = do
    `R ← RecDToType R
    extendContext (vArg `R) do
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
  dT             ← fromTelType (Param Desc.++ Index) (Set level)
  return $ pars , dT , `Param

levels : ℕ → Telescope
levels zero    = []
levels (suc n) = ("_" , hArg `Level) ∷ levels n

defineByDataD : DataD → Name → List Name → TC _
defineByDataD D d cs = let open DataD D in extendContextℓs #levels λ ℓs → do
  let `Levels = levels #levels
  let Dᵖ      = applyL ℓs
  pars , dT , `Param ← getSignature Dᵖ
  declareData d (#levels + pars) (prefixToType `Levels dT)

  conTs ← map (prefixToType `Levels) <$> getCons d pars `Param Dᵖ
  defineData d (zip cs conTs)
