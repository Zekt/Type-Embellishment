open import Prelude
  hiding (_++_)

module Metalib.Datatype where

open import Prelude.List as L
open import Utils.Reflection as Refl

open import Generics.Telescope   as Desc
open import Generics.Description as Desc

open import Metalib.Telescope as Tel

-- Translate the semantics of an object-level telescope to
-- a context
idxToArgs : {T : Tel ℓ} → ⟦ T ⟧ᵗ → TC Context
idxToArgs {T = []}    tt        = return []
idxToArgs {T = _ ∷ _} (x , ⟦T⟧) = do
  `T ← idxToArgs ⟦T⟧
  `x ← quoteTC x
  return (vArg `x ∷ `T)

module _ (dataName : Name) (pars : ℕ) {T : Tel ℓ} where
  unknowns : Args Term
  unknowns = duplicate pars (vArg unknown)

  RecDToType : {B : RecB} → RecD ⟦ T ⟧ᵗ B → TC Type
  RecDToType (ι i) = do
    idxs ← idxToArgs i
    return $ def dataName (unknowns L.++ idxs)
  RecDToType (π A D) = extendContextT visible-relevant-ω A λ `A x → do
      vΠ[ `A ]_ <$> RecDToType (D x)

  ConDToType : {B : ConB} → ConD ⟦ T ⟧ᵗ B → TC Type
  ConDToType (ι i) = do
    idxs ← idxToArgs i
    return $ def dataName (unknowns L.++ idxs)
  ConDToType (σ A D) = extendContextT visible-relevant-ω A λ `A x → do
      vΠ[ `A ]_ <$>  ConDToType (D x)
  ConDToType (ρ R D) = do
    `R ← RecDToType R
    --dprint [ strErr $ "ρ: " <> showTerm `R ]
    extendContext (vArg (quoteTerm ⊤)) do
    -- we might still need to give a correct type to it
      vΠ[ `R ]_ <$> ConDToType D

  ConDsToTypes : {Bs : ConBs} → ConDs ⟦ T ⟧ᵗ Bs → TC Types
  ConDsToTypes []       = return []
  ConDsToTypes (D ∷ Ds) = ⦇ ConDToType D ∷ ConDsToTypes Ds ⦈

defineByPDataD : Name → List Name → PDataD → TC (ℕ × Type × List Type)
defineByPDataD dataName conNames dataD = do
  pars , `Param ← fromTel Param
  dataT         ← fromTelType (Param Desc.++ Index) (Set level)
  extendContextTs Param λ ⟦par⟧ → do
    conTs ← ConDsToTypes dataName pars $ applyP ⟦par⟧
    return $ pars , dataT , map (prefixToType `Param) conTs
  where open PDataD dataD

levels : ℕ → Telescope
levels zero    = []
levels (suc n) = ("_" , hArg `Level) ∷ levels n

defineByDataD : DataD → Name → List Name → TC _
defineByDataD dataD dataName conNames = extendContextℓs #levels λ ℓs → do
  pars , dataT , conTs ← defineByPDataD dataName conNames $ applyL ℓs
  declareData dataName
              (#levels + pars)
              (prefixToType (levels #levels) dataT)
  defineData dataName
               (zip conNames $ map (prefixToType $ levels #levels) conTs)
  where open DataD dataD
