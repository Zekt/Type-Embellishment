{-# OPTIONS -v meta:5 #-}

open import Prelude hiding (length)

module Metalib.Telescope where

open import Utils.Reflection
open import Generics.Description

dprint = debugPrint "meta" 5

-- Frequently used terms
_`∷_ : Term → Term → Term
t `∷ u = con (quote Tel._∷_) (vArg t ∷ vArg u ∷ [])

`[] : Term
`[] = quoteTerm Tel.[]

--
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

length : Tel ℓ → TC ℕ
length [] = return 0
length (A ∷ tel) = do
  a ← quoteTC A
  extendContext (vArg a) $ do
    a' ← unquoteTC (var₀ 0)
    suc <$> length (tel a')

