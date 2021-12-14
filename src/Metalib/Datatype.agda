open import Prelude

module Metalib.Datatype where

open import Utils.Reflection as Refl
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

argVars : ℕ → (weakenBy : ℕ) → List (Arg Term)
argVars zero    wk = []
argVars (suc N) wk = vArg (var₀ (N + wk)) ∷ argVars N wk

--depth is the level without params
module _ (dataName : Name) (pars : ℕ) where

  RecDToType : ∀ {tel : Tel ℓ} {b : RecB}
             → ℕ → RecD ⟦ tel ⟧ᵗ b → TC Type

  RecDToType depth (ι i) = do
    idxs ← idxToArgs i
    return (def dataName (argVars pars depth Prelude.++ idxs))

  RecDToType depth (π A D) = do
    `A ← quoteTC! A
    extendContext (vArg `A) $ do
      `D ← RecDToType (suc depth) ∘ D =<< unquoteTC (var₀ 0)
      return (vΠ[ `A ] `D)

  ConDToType : ∀ {b : ConB} → {tel : Tel ℓ}
             → ℕ → ConD ⟦ tel ⟧ᵗ b → TC Type

  ConDToType depth (ι i) = do
    idxs ← idxToArgs i
    let end = def dataName (argVars pars depth Prelude.++ idxs)
    --dprint [ strErr $ "ι: " <> showTerm end ]
    return end

  ConDToType depth (σ A D) = do
    `A ← quoteTC! A
    --dprint [ strErr $ "σ: " <> showTerm `A ]
    extendContext (vArg `A) $ do
      `D ← ConDToType (suc depth) ∘ D =<< unquoteTC (var₀ 0)
      return (vΠ[ `A ] `D)

  ConDToType depth (ρ R D) = do
    `R ← RecDToType depth R
    --dprint [ strErr $ "ρ: " <> showTerm `R ]
    extendContext (vArg (quoteTerm ⊤)) $ do
      `D ← ConDToType (suc depth) D
      return (vΠ[ `R ] `D)

  ConDsToTypes : {tel : Tel ℓ} {Bs : ConBs}
               → ℕ → ConDs ⟦ tel ⟧ᵗ Bs → TC (List Type)
  ConDsToTypes depth [] = return []
  ConDsToTypes depth (D ∷ Ds) = ⦇ ConDToType depth D ∷ ConDsToTypes depth Ds ⦈

defineDataByDescription : Name → List Name → PDataD → TC (ℕ × Type × List Type)
defineDataByDescription
  dataName
  conNames
  record { plevel = plevel
         ; ilevel = ilevel
         ; struct = struct
         ; level = level
         ; level-pre-fixed-point = level-pre-fixed-point
         ; Param = Param
         ; Index = Index
         ; applyP = Desc } = do
  parType ← uncurry telescopeToType =<< toTelescope Param (Set level)
  dataType ← uncurry telescopeToType  =<< toTelescope (Param Desc.++ Index) (Set level)
  parLen ← Tel.length Param
  auxᵗ Param $ λ ⟦par⟧ → do
    conTypes ← ConDsToTypes dataName parLen 0 (Desc ⟦par⟧)
    return (parLen , dataType , map (Refl._++_ parType) conTypes)
  where
    auxᵗ : ∀ {a : Set ℓ'} → (T : Tel ℓ) → (⟦ T ⟧ᵗ → TC a) → TC a
    auxᵗ [] cont = cont tt
    auxᵗ (A ∷ T) cont = extendContextT visible-relevant-ω A λ _ a →
                        auxᵗ (T a) (curry cont a)

defineDataByDescription' : Name → List Name → DataD → TC _
defineDataByDescription' dataName conNames record { #levels = #levels
                                                  ; applyL = applyL
                                                  } =
  auxℓ #levels $ λ ℓs → do
    (parLen , dataType , conTypes) ← defineDataByDescription dataName conNames (applyL ℓs)
    dataType! ← normalise $ dataType
    declareData dataName (#levels + parLen) (levels #levels Refl.++ dataType!)
    dprint [ strErr $ showTerms (map (vArg ∘ Refl._++_ (levels #levels)) conTypes) ]
    defineData dataName $ zip conNames $ map (Refl._++_ (levels #levels)) conTypes
  where
    auxℓ : ∀ {A : Set ℓ} → (#levels : ℕ) → (Level ^ #levels → TC A) → TC A
    auxℓ zero cont = cont tt
    auxℓ (suc #levels) cont = extendContextT hidden-relevant-ω Level λ _ ℓ →
                              auxℓ #levels (curry cont ℓ)

    levels : ℕ → Term
    levels zero = unknown
    levels (suc n) = hΠ[ quoteTerm Level ] levels n
