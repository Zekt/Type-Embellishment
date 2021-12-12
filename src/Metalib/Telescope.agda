{-# OPTIONS -v meta:5 #-}

open import Prelude

module Metalib.Telescope where

open import Utils.Reflection
open import Generics.Description

dprint = debugPrint "meta" 5

-- Special append that discards the last term in t₁
appendPi : Term → Term → Term
appendPi (pi a (abs _ b)) t₂ = pi a (abs "" (appendPi b t₂))
appendPi _ t₂ = t₂

-- Frequently used terms
_`∷_ : Term → Term → Term
t `∷ u = con (quote Tel._∷_) (vArg t ∷ vArg u ∷ [])

`[] : Term
`[] = quoteTerm Tel.[]

--
CxtToPi : Level → Context → TC Term
CxtToPi ℓ [] = quoteTC! (Set ℓ)
CxtToPi ℓ (x ∷ cxt') = pi x ∘ abs "" <$> CxtToPi ℓ cxt'

toTelescope : Tel ℓ → TC Telescope
toTelescope []      = return []
toTelescope (A ∷ T) = caseM withNormalisation true (quoteTC T) of λ where
  (lam v (abs s _)) → extendContextT (visible-relevant-ω) A λ `A x → do
    `Γ ← toTelescope (T x)
    return $ (s , vArg `A) ∷ `Γ
  t                 → typeError $ strErr (show t) ∷ strErr " cannot be reduced further to a λ-abstraction" ∷ []

fromTelescope : Telescope → TC (Tel ℓ)
fromTelescope = unquoteTC ∘ foldr `[] λ where
    (s , arg _ `A) `T → `A `∷ (`vλ s `→ `T)

macro
  getTelescopeT : Name → Tactic
  getTelescopeT s = evalTC $ getDefType s

idxToArgs : {tel : Tel ℓ} → ⟦ tel ⟧ᵗ → TC (List (Arg Term))
idxToArgs {tel = []} tt = return []
idxToArgs {tel = A ∷ tel} (a , ⟦tel⟧) = do
  tel' ← idxToArgs ⟦tel⟧
  a' ← quoteTC a
  return (vArg a' ∷ tel')

lengthTel : Tel ℓ → TC ℕ
lengthTel [] = return 0
lengthTel (A ∷ tel) = do
  a ← quoteTC A
  extendContext (vArg a) $ do
    a' ← unquoteTC (var₀ 0)
    suc <$> lengthTel (tel a')

argVars : ℕ → (weakenBy : ℕ) → List (Arg Term)
argVars zero    wk = []
argVars (suc N) wk = vArg (var₀ (N + wk)) ∷ argVars N wk

fakeCxt : (tel : Tel ℓ) → ℕ → TC ⟦ tel ⟧ᵗ
fakeCxt [] 0 = return tt
fakeCxt (A ∷ tel) (suc n) = do
  a ← unquoteTC (var₀ n)
  cxt ← fakeCxt (tel a) n
  return {TC} {TC} (a , cxt)
fakeCxt _ _ = typeError [ strErr "IMPOSSIBLE" ]

append : (tel : Tel ℓ) → (⟦ tel ⟧ᵗ → Tel ℓ') → Tel (ℓ ⊔ ℓ')
append [] tel' = tel' tt
append (A ∷ tel) tel' = A ∷ λ a → append (tel a) λ ⟦tel⟧ → tel' (a , ⟦tel⟧)

--depth is the level without params
module _ (dataName : Name) (pars : ℕ) where

  RecDToType : ∀ {tel : Tel ℓ} {b : RecB}
             → ℕ → RecD ⟦ tel ⟧ᵗ b → TC Type

  RecDToType depth (ι i) = do
    idxs ← idxToArgs i
    return (def dataName (argVars pars depth ++ idxs))

  RecDToType depth (π A D) = do
    `A ← quoteTC! A
    extendContext (vArg `A) $ do
      `D ← RecDToType (suc depth) ∘ D =<< unquoteTC (var₀ 0)
      return (vΠ[ `A ] `D)

  ConDToType : ∀ {b : ConB} → {tel : Tel ℓ}
             → ℕ → ConD ⟦ tel ⟧ᵗ b → TC Type

  ConDToType depth (ι i) = do
    idxs ← idxToArgs i
    let end = def dataName (argVars pars depth ++ idxs)
    dprint [ strErr $ "ι: " <> showTerm end ]
    return end

  ConDToType depth (σ A D) = do
    `A ← quoteTC! A
    dprint [ strErr $ "σ: " <> showTerm `A ]
    extendContext (vArg `A) $ do
      `D ← ConDToType (suc depth) ∘ D =<< unquoteTC (var₀ 0)
      return (vΠ[ `A ] `D)

  ConDToType depth (ρ R D) = do
    `R ← RecDToType depth R
    dprint [ strErr $ "ρ: " <> showTerm `R ]
    extendContext (vArg `R) $ do
      `D ← ConDToType (suc depth) D
      return (vΠ[ `R ] `D)

  ConDsToTypes : {tel : Tel ℓ} {Bs : ConBs}
               → ℕ → ConDs ⟦ tel ⟧ᵗ Bs → TC (List Type)
  ConDsToTypes depth [] = return []
  ConDsToTypes depth (D ∷ Ds) = ⦇ ConDToType depth D ∷ ConDsToTypes depth Ds ⦈

defineDataByDescription : Name → List Name → PDataD → TC _
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
  parTel ← toTelescope Param
  parType ← CxtToPi level (⇑ parTel)
  dataTypeTel ← toTelescope (append Param Index)
  dataType ← CxtToPi level (⇑ dataTypeTel)
  inContext (⇑ parTel) $ do
    parLen ← lengthTel Param
    declareData dataName parLen dataType
    ⟦par⟧ ← fakeCxt Param parLen
    conTypes ← ConDsToTypes dataName parLen 0 (Desc ⟦par⟧)
    defineData dataName $ zip conNames $ map (appendPi parType) conTypes
