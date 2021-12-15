open import Prelude
  hiding (_++_)

module Metalib.Datatype where

open import Prelude.List as L
open import Utils.Reflection as Refl

open import Generics.Telescope   as Desc
open import Generics.Description as Desc

open import Metalib.Telescope as Tel

levels : ℕ → Term
levels zero = unknown
levels (suc n) = hΠ[ quoteTerm Level ] levels n

extendContextℓs : {A : Set ℓ} → (#levels : ℕ) → (Level ^ #levels → TC A) → TC A
extendContextℓs zero          cont = cont tt
extendContextℓs (suc #levels) cont =
  extendContextT hidden-relevant-ω Level λ _ ℓ →
    extendContextℓs #levels (curry cont ℓ)

telescopeToType : Telescope → Type → TC Term
telescopeToType [] end = return end
telescopeToType ((s , x) ∷ tel) end = pi x ∘ abs s <$> telescopeToType tel end

idxToArgs : {tel : Tel ℓ} → ⟦ tel ⟧ᵗ → TC Context
idxToArgs {tel = []} tt = return []
idxToArgs {tel = A ∷ tel} (a , ⟦tel⟧) = do
  tel' ← idxToArgs ⟦tel⟧
  a' ← quoteTC a
  return (vArg a' ∷ tel')

--depth is the level without params
module _ (dataName : Name) (pars : ℕ) where
  unknowns : Args Term
  unknowns = duplicate pars (vArg unknown)

  RecDToType : {T : Tel ℓ} {B : RecB}
             → RecD ⟦ T ⟧ᵗ B → TC Type

  RecDToType (ι i) = do
    idxs ← idxToArgs i
    return (def dataName (unknowns L.++ idxs))

  RecDToType (π A D) = extendContextT visible-relevant-ω A λ `A x → do
      vΠ[ `A ]_ <$> RecDToType (D x)

  ConDToType : {b : ConB} → {tel : Tel ℓ}
             → ConD ⟦ tel ⟧ᵗ b → TC Type

  ConDToType (ι i) = do
    idxs ← idxToArgs i
    --let end = def dataName (unknowns L.++ idxs)
    --dprint [ strErr $ "ι: " <> showTerm end ]
    return $ def dataName (unknowns L.++ idxs)

  ConDToType (σ A D) = extendContextT visible-relevant-ω A λ `A x → do
      vΠ[ `A ]_ <$>  ConDToType (D x)

  ConDToType (ρ R D) = do
    `R ← RecDToType R
    --dprint [ strErr $ "ρ: " <> showTerm `R ]
    extendContext (vArg (quoteTerm ⊤)) $ do
      vΠ[ `R ]_ <$> ConDToType D

  ConDsToTypes : {T : Tel ℓ} {Bs : ConBs}
    → ConDs ⟦ T ⟧ᵗ Bs → TC (List Type)
  ConDsToTypes []       = return []
  ConDsToTypes (D ∷ Ds) = ⦇ ConDToType D ∷ ConDsToTypes Ds ⦈

defineByPDataD : Name → List Name → PDataD → TC (ℕ × Type × List Type)
defineByPDataD dataName conNames dataD = do
  parType  ← uncurry telescopeToType
               =<< toTelescope Param (Set level)
  dataType ← uncurry telescopeToType
               =<< toTelescope (Param Desc.++ Index) (Set level)
  parLen   ← Tel.length Param
  extendContextTs Param $ λ ⟦par⟧ → do
    conTypes ← ConDsToTypes dataName parLen (applyP ⟦par⟧)
    return (parLen , dataType , map (parType `++_) conTypes)
  where
    open PDataD dataD

defineByDataD : DataD → Name → List Name → TC _
defineByDataD dataD dataName conNames =
  extendContextℓs #levels $ λ ℓs → do
    (parLen , dataType , conTypes)
      ← defineByPDataD dataName conNames (applyL ℓs)
    declareData dataName
                (#levels + parLen)
                (levels #levels `++ dataType)
    defineData dataName
               (zip conNames $ map (levels #levels `++_) conTypes)
  where
    open DataD dataD
