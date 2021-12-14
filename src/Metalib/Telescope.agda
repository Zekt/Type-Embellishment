{-# OPTIONS -v meta:5 #-}

open import Prelude hiding (length)

module Metalib.Telescope where

open import Utils.Reflection

open import Generics.Telescope
open import Generics.Description

dprint = debugPrint "meta" 5

-- Frequently used terms
_`∷_ : Term → Term → Term
t `∷ u = con (quote Tel._∷_) (vArg t ∷ vArg u ∷ [])

`[] : Term
`[] = quoteTerm Tel.[]

--
toTelescope : Tel ℓ → Set ℓ' → TC (Telescope × Type)
toTelescope []      end = quoteTC! end >>= λ `end →
                          return ([] , `end)
toTelescope (A ∷ T) end = caseM withNormalisation true (quoteTC T) of λ where
  (lam v (abs s _)) → extendContextT (visible-relevant-ω) A λ `A x → do
    `Γ , `end ← toTelescope (T x) end
    return $ ((s , vArg `A) ∷ `Γ , `end)
  t                 → typeError $ strErr (show t) ∷ strErr " cannot be reduced further to a λ-abstraction" ∷ []

fromTelescope : Telescope → TC (Tel ℓ)
fromTelescope = unquoteTC ∘ foldr `[] λ where
    (s , arg _ `A) `T → `A `∷ (`vλ s `→ `T)

-- this may fail if `Tel` is not built by λ by pattern matching lambdas.
length : Tel ℓ → TC ℕ
length []      = return 0
length (A ∷ T) = extendContextT (visible-relevant-ω) A
  λ _ x → suc <$> length (T x)

-- extend the context in a TC computation 
extendContextTs : {A : Set ℓ′}
  → (T : Tel ℓ) → (⟦ T ⟧ᵗ → TC A) → TC A
extendContextTs []      f = f tt
extendContextTs (A ∷ T) f = extendContextT visible-relevant-ω A λ _ x →
  extendContextTs (T x) (curry f x)
