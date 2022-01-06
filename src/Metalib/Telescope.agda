{-# OPTIONS --without-K #-}

open import Prelude hiding (length)

module Metalib.Telescope where

open import Utils.Reflection
open import Utils.Error as Err

open import Generics.Telescope
open import Generics.Description

dprint = debugPrint "meta" 5

-- Frequently used terms
private
  _`∷_ : Term → Term → Term
  t `∷ u = con (quote Tel._∷_) (vArg t ∷ vArg u ∷ [])

  `[] : Term
  `[] = quoteTerm Tel.[]

-- extend the context in a TC computation 
extendCxtTel : {A : Set ℓ′}
  → (T : Tel ℓ) → (⟦ T ⟧ᵗ → TC A) → TC A
extendCxtTel [] f      = f tt
extendCxtTel (A ∷ T) f = do
  s ← getAbsName T
  extendContextT s visible-relevant-ω A λ _ x → extendCxtTel (T x) (curry f x)
extendCxtTel (T ++ U) f = extendCxtTel T λ ⟦T⟧ →
  extendCxtTel (U ⟦T⟧) λ x → curry f ⟦T⟧ x

extendContextℓs : {A : Set ℓ}
  → (#levels : ℕ) → (Level ^ #levels → TC A) → TC A
extendContextℓs zero    c = c tt
extendContextℓs (suc n) c = extendContextT "ℓ" hidden-relevant-ω Level λ _ ℓ →
    extendContextℓs n (curry c ℓ)

-- ℕ is the length of (T : Tel ℓ)
-- this may fail if `Tel` is not built by λ by pattern matching lambdas.
fromTel : Tel ℓ → TC (ℕ × Telescope)
fromTel []      = return (0 , [])
fromTel (A ∷ T) = do
  s ← getAbsName T
  extendContextT s (visible-relevant-ω) A λ `A x → do
    n , `Γ ← fromTel (T x) 
    return $ (suc n) , (s , vArg `A) ∷ `Γ 
fromTel (T ++ U) = do
  n , `Γ ← fromTel T
  extendCxtTel T λ x → do
    m , `Δ ← fromTel (U x)
    return (n + m , `Γ <> `Δ)

to`Tel : Telescope → Term
to`Tel = foldr `[] λ where
  (s , arg _ `A) `T →  `A `∷ vLam (abs s `T)

fromTelescope : Telescope → TC (Tel ℓ)
fromTelescope = unquoteTC ∘ to`Tel
