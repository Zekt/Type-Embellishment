{-# OPTIONS -v meta:5 #-}

open import Prelude

module Metalib.Inductive-ConsTel where

open import Utils.Reflection
open import Generics.Description

dprint = debugPrint "meta" 5

-- Frequently used terms
_`∷_ : Arg Term → Term → Term
t `∷ u = con (quote Tel._∷_) (t ∷ vArg u ∷ [])

`[] : Term
`[] = quoteTerm Tel.[]

-- 

toTelescope : Tel ℓ → TC Telescope
toTelescope []      = return []
toTelescope (A ∷ T) = do
  lam v (abs s _) ← quoteTC T 
    where _ → IMPOSSIBLE
  extendContextT (visible-relevant-ω) A λ `A x → do
    `Γ ← toTelescope (T x)
    return $ (s , vArg `A) ∷ `Γ

fromTelescope : Telescope → TC (Tel ℓ)
fromTelescope = unquoteTC ∘ foldr `[] λ where
    (s , `A) `T → vArg (unArg `A) `∷ (vλ s ↦ `T)
