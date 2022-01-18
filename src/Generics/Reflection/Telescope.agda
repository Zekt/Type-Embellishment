{-# OPTIONS --safe --without-K #-}

open import Prelude

module Generics.Reflection.Telescope where
open import Utils.Reflection
open import Utils.Error as Err

open import Generics.Telescope

-- Frequently used terms
private
  variable
    T U : Tel ℓ
  
  _`∷_ : Term → Term → Term
  t `∷ u = con (quote Tel._∷_) (vArg t ∷ vArg u ∷ [])

  `[] : Term
  `[] = quoteTerm Tel.[]

-- extend the context in a TC computation 
extendCxtTel : {A : Set ℓ′}
  → (T : Tel ℓ) → (⟦ T ⟧ᵗ → TC A) → TC A
extendCxtTel [] f      = f tt
extendCxtTel (A ∷ T) f = do
--  s ← getAbsNameω T
  extendContextT "_" visible-relevant-ω A λ _ x → extendCxtTel (T x) (curry f x)
extendCxtTel (T ++ U) f = extendCxtTel T λ ⟦T⟧ →
  extendCxtTel (U ⟦T⟧) λ x → curry f ⟦T⟧ x

extendContextℓs : {A : Set ℓ}
  → (#levels : ℕ) → (Level ^ #levels → TC A) → TC A
extendContextℓs zero    c = c tt
extendContextℓs (suc n) c = extendContextT "ℓ" hidden-relevant-ω Level λ _ ℓ →
    extendContextℓs n (curry c ℓ)

-- ℕ is the length of (T : Tel ℓ)
-- this may fail if `Tel` is not built by λ by pattern matching lambdas.
fromTel : {ℓ : Level}
  → Tel ℓ → TC Telescope
fromTel []      = return []
fromTel (A ∷ T) = do
--  s ← getAbsNameω T
  extendContextT "_" (visible-relevant-ω) A λ `A x → do
    Γ ← fromTel (T x)
    return $ ("_" , vArg `A) ∷ Γ
fromTel (T ++ U) = do
  `Γ ← fromTel T
  extendCxtTel T λ x → do
    `Δ ← fromTel (U x)
    return (`Γ <> `Δ)

to`Tel : Telescope → Term
to`Tel = foldr `[] λ where
  (s , arg _ `A) `T →  `A `∷ vLam (abs s `T)

macro
  genTel : Telescope → Tactic
  genTel Γ hole = do
    `ℓ ← newMeta `Level
    checkedHole ← checkType hole (def₁ (quote Tel) `ℓ)
    unify checkedHole (to`Tel Γ)

-- Check if the given telescope is a prefix of a telescope up to arg-info 
-- and return the telescope with the correct visibility
-- `T ⊆ᵗ? Γ` returns
--   1. a telescope corresponding to T (with `arg-info` copied from Γ) and
--   2. the telescope of Γ without T
_⊆ᵗ?_ : Tel ℓ → Telescope → TC (Telescope × Telescope)
[]      ⊆ᵗ? Γ  = return ([] , Γ)
(A ∷ T) ⊆ᵗ? [] = do
  `A ← quoteTC A
  typeError $ 
    strErr "An extra argument of type" ∷ termErr `A ∷ strErr " to apply" ∷ []
(A ∷ T) ⊆ᵗ? ((s , arg i@(arg-info v m) `B) ∷ Γ) = do
  `A ← quoteTC! A
--   dprint $ [ termErr `A ]
--   dprint $ [ termErr `B ]
  unify `A `B <|> (typeError $ termErr `A ∷ strErr " ≠ " ∷ termErr `B ∷ [])
  extendContextT s i A λ _ x → bimap ((s , arg i `B) ∷_) id <$> T x ⊆ᵗ? Γ
(T ++ U) ⊆ᵗ? Γ = do
  (vs , Γ) ← T ⊆ᵗ? Γ
  extendCxtTel T λ t → do
    (vs′ , Γ) ← U t ⊆ᵗ? Γ
    return (vs <> vs′ , Γ)

------------------------------------------------------------------------
-- Each constructor `c : (x₁ : A₁) → (x₂ : A₂ x₁) → ⋯ → T`
-- can be represented as a pattern on the LHS `c x₁ x₂ ⋯ xₙ` or as a term on the RHS
-- They can be also uncurried described by ⟦ ConD ⟧. Thus, there are 4 types of constructor representations. 
cxtToVars : (from : ℕ) → (base : Term × Pattern) → (Γ : Telescope) → (Term × Pattern) × (Args Term × Args Pattern)
cxtToVars from base = snd ∘ foldr emptyVar λ where
      (_ , arg i _) (n , (t , p) , (targs , pargs)) →
        suc n , ((var₀ n `, t) , (var n `, p)) , (arg i (var₀ n) ∷ targs) , (arg i (var n) ∷ pargs)
  where emptyVar = from , base , [] , []

cxtToVarPatt : Telescope → Pattern
cxtToVarPatt Γ = let (_ , p) , _ = cxtToVars 0 (`tt , `tt) Γ in p

------------------------------------------------------------------------
-- 

telToVars : (from : ℕ) (base : Term × Pattern)
  → (T : Tel ℓ) (Γ : Telescope) → TC $ (Term × Pattern) × (Args Term × Args Pattern)
telToVars from base T Γ = snd <$> go from base T Γ 
  where 
    go : (from : ℕ) (base : Term × Pattern)
      → (T : Tel ℓ) (Γ : Telescope)
      → TC $ ℕ × (Term × Pattern) × (Args Term × Args Pattern)
    go from base []       _       = return (from , base , [] , [])
    go from base (A ∷ T)  []      = typeError
      $ strErr "The length of Tel is different from the length of Telescope" ∷ []
    go from base (A ∷ T)  ((s , arg i B) ∷ Γ) = do
      `A ← quoteTC! A
      extendContextT s i A λ _ x → do
        n , (t , p) , (targs , pargs) ← go from base (T x) Γ
        return $ suc n , ((var₀ n `, t) , (var n `, p)) , arg i (var₀ n) ∷ targs , arg i (var n) ∷ pargs
    go from base (T ++ U) Γ = do
      n ← length <$> fromTel T
      let (Γ , Δ) = splitAt n Γ
      n , (Δt , Δp) , Δts , Δps ← extendCxtTel T λ t → go from base (U t) Δ
      m , (Γt , Γp) , Γts , Γps ← go n base T Γ 
      return $ m , ((Γt `, Δt) , (Γp `, Δp)) , (Γts <> Δts , Γps <> Δps)
      
-- Translate the semantics of an object-level telescope to a context
idxToArgs : ⟦ T ⟧ᵗ → TC (Args Term)
idxToArgs {T = []}     tt      = ⦇ [] ⦈
idxToArgs {T = _ ∷ _}  (A , Γ) = ⦇ ⦇ vArg (quoteTC A) ⦈ ∷ (idxToArgs Γ) ⦈
idxToArgs {T = _ ++ _} (T , U) = ⦇ (idxToArgs T) <> (idxToArgs U) ⦈

-- ... and back
argsToIdx : Args Term → Term
argsToIdx []       = `tt
argsToIdx (x ∷ xs) = (unArg x) `, argsToIdx xs

-- The fully applied datatype 
typeOfData : Name → (ps : ⟦ U ⟧ᵗ) (is : ⟦ T ⟧ᵗ) → TC Type 
typeOfData d ps is = ⦇ (def d) ⦇ (idxToArgs ps) <> (idxToArgs is) ⦈ ⦈ 
