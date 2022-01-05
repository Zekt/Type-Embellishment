{-# OPTIONS --without-K #-}

open import Prelude hiding (length)

module Metalib.Telescope where

open import Utils.Reflection
open import Utils.Error as Err

open import Generics.Telescope hiding (fromMTel)
open import Generics.Description

dprint = debugPrint "meta" 5

-- Frequently used terms
private
  _`∷_ : Term → Term → Term
  t `∷ u = con (quote MTel._∷_) (vArg t ∷ vArg u ∷ [])

  `[] : Term
  `[] = quoteTerm MTel.[]

-- extend the context in a TC computation 
extendCxtTel : {A : Set ℓ′}
  → (T : Tel ℓ) → (⟦ T ⟧ᵗ → TC A) → TC A
extendCxtTel []      f = f tt
extendCxtTel (A ∷ T) f = extendContextT "x" visible-relevant-ω A λ _ x →
  extendCxtTel (T x) (curry f x)

extendCxtMTel : {A : Set ℓ′}
  → (T : MTel ℓ) → (⟦ T ⟧ᵐᵗ → TC A) → TC A
extendCxtMTel [] f = f tt
extendCxtMTel (A ∷ T) f = extendContextT "x" visible-relevant-ω A λ _ x →
  extendCxtMTel (T x) (curry f x)
extendCxtMTel (MT ++ MT') f = extendCxtMTel MT λ ⟦MT⟧ →
  extendCxtMTel (MT' ⟦MT⟧) λ x → curry f ⟦MT⟧ x

extendContextℓs : {A : Set ℓ}
  → (#levels : ℕ) → (Level ^ #levels → TC A) → TC A
extendContextℓs zero    c = c tt
extendContextℓs (suc n) c = extendContextT "ℓ" hidden-relevant-ω Level λ _ ℓ →
    extendContextℓs n (curry c ℓ)

-- ℕ is the length of (T : Tel ℓ)
-- this may fail if `Tel` is not built by λ by pattern matching lambdas.
fromTel : (T : Tel ℓ) → TC (ℕ × Telescope)
fromTel []      = return (0 , [])
fromTel (A ∷ T) = caseM quoteTC! T of λ where
  (lam v (abs s _)) → extendContextT s (visible-relevant-ω) A λ `A x → do
    n , `Γ ← fromTel (T x) 
    return $ (suc n) , (s , vArg `A) ∷ `Γ 
  t                 → Err.notλ t

fromMTel : MTel ℓ → TC (ℕ × Telescope)
fromMTel []      = return (0 , [])
fromMTel (A ∷ T) = caseM quoteTC! T of λ where
  (lam v (abs s _)) → extendContextT s (visible-relevant-ω) A λ `A x → do
    n , `Γ ← fromMTel (T x) 
    return $ (suc n) , (s , vArg `A) ∷ `Γ 
  t                 → Err.notλ t
fromMTel (MT ++ MT') = do
  n , `Γ ← fromMTel MT
  extendCxtMTel MT λ x → do
    m , `Δ ← fromMTel (MT' x)
    return (n + m , `Γ <> `Δ)

fromMTelType : MTel ℓ → Set ℓ′ → TC Type
fromMTelType T B = do
  _ , tel ← fromMTel T
  extendCxtMTel T λ _ → do
    `B ← quoteTC! B
    return (⇑ (tel , `B))

to`MTel : Telescope → Term
to`MTel = foldr `[] λ where
  (s , arg _ `A) `T →  `A `∷ vLam (abs s `T)

fromTelescope : Telescope → TC (MTel ℓ)
fromTelescope = unquoteTC ∘ to`MTel

