{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude as P

module Metalib.Datatype where

open import Utils.Reflection as Refl
open import Utils.Error as Err

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
    return (def dataName (argVars pars depth P.++ idxs))

  RecDToType depth (π A D) = extendContextT visible-relevant-ω A λ `A x → do
      `D ← RecDToType (suc depth) (D x)
      return (vΠ[ `A ] `D)

  ConDToType : ∀ {b : ConB} → {tel : Tel ℓ}
             → ℕ → ConD ⟦ tel ⟧ᵗ b → TC Type

  ConDToType depth (ι i) = do
    idxs ← idxToArgs i
    let end = def dataName (argVars pars depth P.++ idxs)
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

defineByPDataD : Name → List Name → PDataD
               → TC (ℕ × Type × List Type)
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

describeByConstructor : {b : ConB} {Index : Tel ℓ} → Name → Type
                      → TC (ConD ⟦ Index ⟧ᵗ b)
describeByConstructor {Index = Index} dataName t = do
  let (tel , end) = ⇑_ ⦃ TypeToTelescope ⦄ t
  return {!!}


--describeByData : ℕ → Type → List Type → TC DataD
--describeByData parLen dataType conTypes = do
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
--
--    splitAcc : Telescope → Telescope → ℕ → (Telescope × Telescope)
--    splitAcc tel₁ [] n = tel₁ , []
--    splitAcc tel₁ tel₂ 0 = tel₁ , tel₂
--    splitAcc tel₁ (x ∷ tel₂) (suc n) = splitAcc (tel₁ P.++ [ x ]) tel₂ n
--    toTel : Telescope → Term
--    toTel []              = quoteTerm Tel.[]
--    toTel ((s , x) ∷ tel) = con (quote Tel._∷_)
--                                (x
--                                ∷ vArg (vLam (abs s (toTel tel)))
--                                ∷ [])
--
--    lamTel : ℕ → Telescope → Term
--    lamTel zero    tel = toTel tel
--    lamTel (suc n) tel = vLam (abs "" (lamTel n tel))

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
