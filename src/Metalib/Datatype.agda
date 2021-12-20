{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude as P

module Metalib.Datatype where

open import Prelude.List as L
open import Utils.Reflection as Refl
open import Utils.Error as Err

open import Generics.Telescope   as Desc
open import Generics.Description as Desc

open import Metalib.Telescope as Tel

telescopeToType : Telescope → Type → TC Term
telescopeToType [] end = return end
telescopeToType ((s , x) ∷ tel) end = pi x ∘ abs s <$> telescopeToType tel end

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

module _ (dataN : Name) (pars : ℕ) {T : Tel ℓ} where
  unknowns : Args Term
  unknowns = duplicate pars (vArg unknown)

  RecDToType : {B : RecB} (R : RecD ⟦ T ⟧ᵗ B) → TC Type
  RecDToType (ι i) = do
    idxs ← idxToArgs i
    return $ def dataN (unknowns L.++ idxs)
  RecDToType (π A D) = extendContextT visible-relevant-ω A λ `A x → do
      vΠ[ `A ]_ <$> RecDToType (D x)

  ConDToType : {B : ConB} (D : ConD ⟦ T ⟧ᵗ B) → TC Type
  ConDToType (ι i) = do
    idxs ← idxToArgs i
    return $ def dataN (unknowns L.++ idxs)
  ConDToType (σ A D) = extendContextT visible-relevant-ω A λ `A x → do
      vΠ[ `A ]_ <$>  ConDToType (D x)
  ConDToType (ρ R D) = do
    `R ← RecDToType R
    --dprint [ strErr $ "ρ: " <> showTerm `R ]
    extendContext (vArg (quoteTerm ⊤)) do
    -- we might still need to give a correct type to it
      vΠ[ `R ]_ <$> ConDToType D

  ConDsToTypes : {Bs : ConBs} (Ds : ConDs ⟦ T ⟧ᵗ Bs) → TC (List Type)
  ConDsToTypes []       = return []
  ConDsToTypes (D ∷ Ds) = ⦇ ConDToType D ∷ ConDsToTypes Ds ⦈

defineByPDataD : Name → PDataD → TC (ℕ × Type × List Type)
defineByPDataD dataN dataD = do
  pars , `Param ← fromTel Param
  dataT         ← fromTelType (Param Desc.++ Index) (Set level)
  extendContextTs Param λ ps ⟦Ps⟧ → do
    conTs ← map (prefixToType `Param)
      <$> ConDsToTypes dataN pars (applyP ⟦Ps⟧)
    return $ pars , dataT , conTs
  where open PDataD dataD

defineByDataD : DataD → Name → List Name → TC _
defineByDataD dataD dataN conNs = extendContextℓs #levels λ `ℓs ℓs → do
  pars , dataT , conTs ← defineByPDataD dataN $ applyL ℓs
  -- dataT and conTs do not contain Level in their types
  let `Levels = levels #levels
  let dataT   = prefixToType `Levels dataT
  let conTs   = prefixToType `Levels <$> conTs

  declareData dataN (#levels + pars) dataT
  defineData  dataN (zip conNs conTs)
  where
    open DataD dataD
    levels : ℕ → Telescope
    levels zero    = []
    levels (suc n) = ("_" , hArg `Level) ∷ levels n

---------
-- should remove parameters in args
argsToIdx : List (Arg Type) → (tel : Tel ℓ) → TC ⟦ tel ⟧ᵗ
argsToIdx [] []       = return tt
argsToIdx [] tel      = Err.#idxNotMatch
argsToIdx (x ∷ ts) [] = Err.#idxNotMatch
argsToIdx (x ∷ ts) (A ∷ T) = do a ← unquoteTC {A = A} (unArg x)
                                ⟦tel⟧ ← argsToIdx ts (T a)
                                return {TC} {TC} (a , ⟦tel⟧)

endsIn : Type → Name → Bool
endsIn (pi a (abs _ b)) u = endsIn b u
endsIn (def f args)     u = f == u
endsIn t                u = false

--showRecD : {b : RecB} {tel : Tel ℓ} → (RecD ⟦ tel ⟧ᵗ b) → TC String
--showRecD {.lzero} {.[]} {[]} (ι i) = return "tt"
--showRecD {.(_ ⊔ _)} {.[]} {A ∷ T₁} (ι (x , y)) = extendContextT visible-relevant-ω A λ typ a → do
--                                                   let str = "ι: "
--                                                   `x ← quoteTC x
--                                                   {!!}
--                                                   return $ showTerm {!!}
--showRecD {ℓ} {b} {tel} (π A D) = {!!}

module _ (dataName : Name) (#levels : ℕ) (parLen : ℕ) where
  telescopeToRecD : Telescope → Type → (tel : Tel ℓ)
                  → TC (Σ RecB λ b → RecD ⟦ tel ⟧ᵗ b)
  telescopeToRecD ((s , arg _ `x) ∷ `tel) end idxTel = do
    ℓ          ← getTypeLevel =<< inferType `x
    x          ← unquoteTC {A = Set ℓ} `x
    (ℓs , rec) ← telescopeToRecD `tel end idxTel
    `rec       ← quoteTC rec
    lamRec     ← unquoteTC $ vLam (abs s `rec)
    return (ℓ ∷ ℓs , π x lamRec)
  telescopeToRecD [] (def f args) idxTel with f == dataName
  ... | true  = argsToIdx (drop parLen args) idxTel >>= λ ⟦idx⟧ →
                return ([] , ι ⟦idx⟧)
  ... | false = Err.notEndIn dataName
  telescopeToRecD [] _ _ = Err.notEndIn dataName


  telescopeToConD : Level → Telescope → Type → (idxTel : Tel ℓ)
                  → TC (Σ ConB λ b → ConD ⟦ idxTel ⟧ᵗ b)
  telescopeToConD ℓ ((s , (arg _ `x)) ∷ `tel) end idxTel
             with endsIn `x dataName
  ... | true = do
    (b , recd)  ← uncurry telescopeToRecD (⇑ `x) idxTel
    (ℓs , cond) ← telescopeToConD ℓ `tel end idxTel
    return (inr b ∷ ℓs , ρ recd cond)
  ... | false = do
   -- dprint [ strErr $ showTerm  `x ]
   -- infx        ← inferType `x
   -- dprint [ strErr $ showTerm  infx ]
   -- ℓ           ← getTypeLevel infx
    x           ← unquoteTC {A = Set ℓ} `x
    extendContext (vArg `x) $ do
      cxt ← getContext
      dprint [ strErr $ "context: " <> showTerms cxt ]
      (ℓs , cond) ← telescopeToConD ℓ `tel end idxTel
      `cond       ← quoteTC cond
      lamConD     ← unquoteTC $ vLam (abs s `cond)
      return (inl ℓ ∷ ℓs , σ x lamConD)
  telescopeToConD ℓ [] (def f args) idxTel with f == dataName
  ... | true  = argsToIdx (drop parLen args) idxTel >>= λ ⟦idx⟧ →
                return ([] , ι ⟦idx⟧)
  ... | false = Err.notEndIn dataName
  telescopeToConD ℓ [] _ _ = Err.notEndIn dataName

  describeByConstructor : {Index : Tel ℓ} → Name
                        → TC (Σ ConB λ b → ConD ⟦ Index ⟧ᵗ b)
  describeByConstructor {Index = Index} conName = do
    --apply conType to levels and parameters
    conType ← getType conName
    let (tel , end) = ⇑_ ⦃ TypeToTelescope ⦄ conType
    let tel' = drop (#levels + parLen) tel
    extendContextℓs 1 λ _ ℓs → do
      extendContextTs (Set lzero ∷ const []) λ _ x → do
        -- constructor type without levels and parameters
        dprint [ strErr $ "telescope: " <> showTerms (map snd tel') ]
        dprint [ termErr (⇑ (tel' , end)) ]
        --let insConType = (con conName (argVars (#levels + parLen) 0))
        --dprint [ strErr $ "constructor type without levels and parameters: " <> showTerm insConType ]
        telescopeToConD {!!} tel' end Index


describeByData : ℕ → Name → List Name → TC DataD
describeByData parLen dataName conNames = do
    dataType ← getType dataName
    conNames ← mapM getType conNames
    let (tel     , end) = ⇑_ ⦃ TypeToTelescope ⦄ dataType
        (#levels , tel) = splitLevels tel
        (par     , idx) = splitAcc [] tel parLen
    parTel ← fromTelescope par
    idxTel ← unquoteTC {A = Curried parTel (const (Tel _))} (lamTel parLen idx)
    level ← {!!} --getLevel end
    return (record { #levels = #levels
                   ; applyL = λ {x →
                       record
                         { level = level
                         ; level-pre-fixed-point = refl
                         ; Param = parTel
                         ; Index = uncurryⁿ parTel (const (Tel _)) idxTel
                         ; applyP = {!!}
                         }}
                   })
  where
    splitLevels : Telescope → (ℕ × Telescope)
    splitLevels [] = 0 , []
    splitLevels t@((_ , arg _ a) ∷ tel) =
      if a == quoteTerm Level then bimap suc id (splitLevels tel)
                              else 0 , t

    splitAcc : Telescope → Telescope → ℕ → (Telescope × Telescope)
    splitAcc tel₁ [] n = tel₁ , []
    splitAcc tel₁ tel₂ 0 = tel₁ , tel₂
    splitAcc tel₁ (x ∷ tel₂) (suc n) = splitAcc (tel₁ P.++ [ x ]) tel₂ n
    toTel : Telescope → Term
    toTel []              = quoteTerm Tel.[]
    toTel ((s , x) ∷ tel) = con (quote Tel._∷_)
                                (x
                                ∷ vArg (vLam (abs s (toTel tel)))
                                ∷ [])

    lamTel : ℕ → Telescope → Term
    lamTel zero    tel = toTel tel
    lamTel (suc n) tel = vLam (abs "" (lamTel n tel))

--getLevel : Term → TC Level
--getLevel (def f args) =
--  if f == quote Set then
--    case args of (λ where
--      []       → return lzero
--      (x ∷ x₁) → unquoteTC (unArg x)
--    )
--  else typeError [ strErr "datatype does not end in Set." ]
--getLevel t = typeError [ strErr "datatype is not canonical." ]
--splitDep ((s , x) ∷ tel₁) tel₂ =
--  let (tel₁' , tel₂') = splitDep tel₁ tel₂
--   in con (quote Tel._∷_) (x ∷ vArg (vLam (abs s tel₁')) ∷ []) , vLam (abs s tel₂')

--ΣTel : ℕ → ℕ → Pattern
--ΣTel n zero    = var n
--ΣTel n (suc m) = con (quote _,_) {!!}
