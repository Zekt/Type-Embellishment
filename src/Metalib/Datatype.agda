open import Prelude
  hiding (_++_)

module Metalib.Datatype where

open import Utils.Reflection as Refl

open import Generics.Telescope   as Desc
open import Generics.Description as Desc

open import Metalib.Telescope as Tel

idxToArgs : {T : Tel ℓ} → ⟦ T ⟧ᵗ → TC Context
idxToArgs {T = []}    tt          = return []
idxToArgs {T = A ∷ _} (x , ⟦T⟧) = do
  `T ← idxToArgs ⟦T⟧
  `x   ← quoteTC x
  return (vArg `x ∷ `T)

-- 
argVars : ℕ → (weakenBy : ℕ) → Args Term
argVars zero    wk = []
argVars (suc N) wk = vArg (var₀ (N + wk)) ∷ argVars N wk

--depth is the level without params
module _ (dataName : Name) (pars : ℕ) where

  RecDToType : ∀ {tel : Tel ℓ} {b : RecB}
             → ℕ → RecD ⟦ tel ⟧ᵗ b → TC Type

  RecDToType depth (ι i) = do
    idxs ← idxToArgs i
    return (def dataName (argVars pars depth Prelude.++ idxs))

  RecDToType depth (π A D) = extendContextT visible-relevant-ω A λ `A x → do
      `D ← RecDToType (suc depth) (D x)
      return (vΠ[ `A ] `D)

  ConDToType : ∀ {b : ConB} → {tel : Tel ℓ}
             → ℕ → ConD ⟦ tel ⟧ᵗ b → TC Type

  ConDToType depth (ι i) = do
    idxs ← idxToArgs i
    let end = def dataName (argVars pars depth Prelude.++ idxs)
    --dprint [ strErr $ "ι: " <> showTerm end ]
    return end

  ConDToType depth (σ A D) = extendContextT visible-relevant-ω A λ `A x → do
      `D ← ConDToType (suc depth) (D x)
      return (vΠ[ `A ] `D)

  ConDToType depth (ρ R D) = do
    `R ← RecDToType depth R
    --dprint [ strErr $ "ρ: " <> showTerm `R ]
    extendContext (vArg (quoteTerm ⊤)) $ do
      `D ← ConDToType (suc depth) D
      return (vΠ[ `R ] `D)

  ConDsToTypes : {T : Tel ℓ} {Bs : ConBs}
               → ℕ → ConDs ⟦ T ⟧ᵗ Bs → TC (List Type)
  ConDsToTypes depth []       = return []
  ConDsToTypes depth (D ∷ Ds) = ⦇ ConDToType depth D ∷ ConDsToTypes depth Ds ⦈

defineByPDataD : Name → List Name → PDataD → TC _
defineByPDataD dataName conNames dataD = do
  `level      ← quoteLevelTC level
  parTel      ← toTelescope Param
  let parType  = ⇑ (parTel , `Set `level)
  dataTypeTel ← toTelescope $ Param ++ Index
  let dataType = ⇑ (dataTypeTel , `Set `level)
  parLen      ← Tel.length Param
  extendContextTs Param $ λ ⟦par⟧ → do
    conTypes    ← ConDsToTypes dataName parLen 0 (applyP ⟦par⟧)
    declareData dataName parLen dataType
    let conTypes = map (parType `++_) conTypes -- LT: This is hacky.
    defineData  dataName $ zip conNames conTypes
  where
    open PDataD dataD
