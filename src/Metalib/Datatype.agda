open import Prelude
  hiding (_++_)

module Metalib.Datatype where

open import Utils.Reflection as Refl

open import Generics.Telescope   as Desc
open import Generics.Description as Desc

open import Metalib.Telescope as Tel

telescopeToType : Telescope → Type → TC Term
telescopeToType [] end = return end
telescopeToType ((s , x) ∷ tel) end = pi x ∘ abs s <$> telescopeToType tel end

idxToArgs : {tel : Tel ℓ} → ⟦ tel ⟧ᵗ → TC Context
idxToArgs {tel = []} tt = return []
idxToArgs {tel = A ∷ tel} (a , ⟦tel⟧) = do
  tel' ← idxToArgs ⟦tel⟧
  a' ← quoteTC a
  return (vArg a' ∷ tel')

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

defineByPDataD : Name → List Name → PDataD → TC (ℕ × Type × List Type)
defineByPDataD dataName conNames dataD = do
  parType  ← uncurry telescopeToType
               =<< toTelescope Param (Set level)
  dataType ← uncurry telescopeToType
               =<< toTelescope (Param Desc.++ Index) (Set level)
  parLen   ← Tel.length Param
  extendContextTs Param $ λ ⟦par⟧ → do
    conTypes ← ConDsToTypes dataName parLen 0 (applyP ⟦par⟧)
    return (parLen , dataType , map (_`++_ parType) conTypes)
  where
    open PDataD dataD

defineByDataD : Name → List Name → DataD → TC _
defineByDataD dataName conNames record { #levels = #levels
                                                  ; applyL = applyL
                                                  } =
  extendContextℓs #levels $ λ ℓs → do
    (parLen , dataType , conTypes)
      ← defineByPDataD dataName conNames (applyL ℓs)
    dataType! ← normalise $ dataType
    declareData dataName
                (#levels + parLen)
                (levels #levels `++ dataType!)
    defineData dataName
               (zip conNames $ map (_`++_ (levels #levels)) conTypes)
  where
    extendContextℓs : ∀ {A : Set ℓ} → (#levels : ℕ) → (Level ^ #levels → TC A) → TC A
    extendContextℓs zero          cont = cont tt
    extendContextℓs (suc #levels) cont = extendContextT hidden-relevant-ω Level λ _ ℓ →
                              extendContextℓs #levels (curry cont ℓ)

    levels : ℕ → Term
    levels zero = unknown
    levels (suc n) = hΠ[ quoteTerm Level ] levels n
