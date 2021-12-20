{-# OPTIONS --without-K #-}

open import Prelude
  hiding (_++_)

module Metalib.Datatype where

open import Prelude.List         as L
open import Utils.Reflection
open import Utils.Error          as Err

open import Generics.Telescope   as Desc
open import Generics.Description as Desc
open import Generics.Levels      as Desc

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
  dT             ← fromTelType (Param Desc.++ Index) (Set dlevel)
  return $ pars , dT , `Param

defineByDataD : DataD → Name → List Name → TC _
defineByDataD D d cs = let open DataD D in extendContextℓs #levels λ ℓs → do
  let `Levels = levels #levels
  let Dᵖ      = applyL ℓs
  pars , dT , `Param ← getSignature Dᵖ
  declareData d (#levels + pars) (prefixToType `Levels dT)

  conTs ← map (prefixToType `Levels) <$> getCons d pars `Param Dᵖ
  defineData d (zip cs conTs)

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

module _ (dataName : Name) (parLen : ℕ) where
  telescopeToRecD : Telescope → Type → (tel : Tel ℓ)
                  → TC (Σ RecB λ b → RecD ⟦ tel ⟧ᵗ b)
  telescopeToRecD ((s , arg _ `x) ∷ `tel) end idxTel = do
    ℓ          ← getLevel =<< inferType `x
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


  telescopeToConD : Telescope → Type → (idxTel : Tel ℓ)
                  → TC (Σ ConB λ b → ConD ⟦ idxTel ⟧ᵗ b)
  telescopeToConD ((s , (arg _ `x)) ∷ `tel) end idxTel
             with endsIn `x dataName
  ... | true = do
    (b , recd)  ← uncurry telescopeToRecD (⇑ `x) idxTel
    (ℓs , cond) ← telescopeToConD `tel end idxTel
    return (inr b ∷ ℓs , ρ recd cond)
  ... | false = do
    ℓ           ← getLevel =<< inferType `x
    x           ← unquoteTC {A = Set ℓ} `x
    (ℓs , cond) ← telescopeToConD `tel end idxTel
    `cond       ← quoteTC cond
    lamConD     ← unquoteTC $ vLam (abs s `cond)
    return (inl ℓ ∷ ℓs , σ x lamConD)
  telescopeToConD [] (def f args) idxTel with f == dataName
  ... | true  = argsToIdx (drop parLen args) idxTel >>= λ ⟦idx⟧ →
                return ([] , ι ⟦idx⟧)
  ... | false = Err.notEndIn dataName
  telescopeToConD [] _ _ = Err.notEndIn dataName

-- describeByConstructor : {b : ConB} {Index : Tel ℓ} → Name → Type
--                       → TC (ConD ⟦ Index ⟧ᵗ b)
-- describeByConstructor {Index = Index} dataName t = do
--   let (tel , end) = ⇑_ ⦃ TypeToTelescope ⦄ t
--   return {!!}


-- describeByData : ℕ → Type → List Type → TC DataD
-- describeByData parLen dataType conTypes = do
--    let (tel     , end) = ⇑_ ⦃ TypeToTelescope ⦄ dataType
--        (#levels , tel) = splitLevels tel
--        (par     , idx) = splitAcc [] tel parLen
--    parTel ← fromTelescope par
--    idxTel ← unquoteTC {A = Curried parTel (const (Tel _))} (lamTel parLen idx)
--    level ← getLevel end
--    return (record { #levels = #levels
--                   ; applyL = λ {x →
--                       record
--                         { level = level
--                         ; level-pre-fixed-point = refl
--                         ; Param = parTel
--                         ; Index = uncurryⁿ parTel (const (Tel _)) idxTel
--                         ; applyP = {!!}
--                         }}
--                   })
--  where
--    splitLevels : Telescope → (ℕ × Telescope)
--    splitLevels [] = 0 , []
--    splitLevels t@((_ , arg _ a) ∷ tel) =
--      if a == quoteTerm Level then bimap suc id (splitLevels tel)
--                              else 0 , t

--    splitAcc : Telescope → Telescope → ℕ → (Telescope × Telescope)
--    splitAcc tel₁ [] n = tel₁ , []
--    splitAcc tel₁ tel₂ 0 = tel₁ , tel₂
--    splitAcc tel₁ (x ∷ tel₂) (suc n) = splitAcc (tel₁ L.++ [ x ]) tel₂ n
--    toTel : Telescope → Term
--    toTel []              = quoteTerm Tel.[]
--    toTel ((s , x) ∷ tel) = con (quote Tel._∷_)
--                                (x
--                                ∷ vArg (vLam (abs s (toTel tel)))
--                                ∷ [])

--    lamTel : ℕ → Telescope → Term
--    lamTel zero    tel = toTel tel
--    lamTel (suc n) tel = vLam (abs "" (lamTel n tel))

-- getLevel : Term → TC Level
-- getLevel (def f args) =
--  if f == quote Set then
--    case args of (λ where
--      []       → return lzero
--      (x ∷ x₁) → unquoteTC (unArg x)
--    )
--  else typeError [ strErr "datatype does not end in Set." ]
-- getLevel t = typeError [ strErr "datatype is not canonical." ]

-- splitDep ((s , x) ∷ tel₁) tel₂ =
--  let (tel₁' , tel₂') = splitDep tel₁ tel₂
--   in con (quote Tel._∷_) (x ∷ vArg (vLam (abs s tel₁')) ∷ []) , vLam (abs s tel₂')

-- ΣTel : ℕ → ℕ → Pattern
-- ΣTel n zero    = var n
-- ΣTel n (suc m) = con (quote _,_) {!!}
