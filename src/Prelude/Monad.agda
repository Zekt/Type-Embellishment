{-# OPTIONS --safe #-}

module Prelude.Monad where

open import Prelude.Level
open import Prelude.Function

open import Prelude.Functor
open import Prelude.Applicative

private variable
  A B : Set _

record Monad (M : ∀ {ℓ} → Set ℓ → Set ℓ) : Setω where
  infixr 0 caseM_of_
  infixr 1 _=<<_
  infixl 1 _>>=_ _>>_
  field
    _>>=_ : M A → (A → M B) → M B
    overlap ⦃ super ⦄ : Applicative M

  _>>_ : M A → M B → M B
  m₁ >> m₂ = m₁ >>= λ _ → m₂

  _=<<_ : (A → M B) → M A → M B
  _=<<_ = flip _>>=_

  return = pure
  join : {A : Set ℓ} → M (M A) → M A
  join = _=<<_ id

  caseM_of_ = _>>=_
open Monad ⦃...⦄ public

{-# DISPLAY Monad._>>=_  _ = _>>=_  #-}
{-# DISPLAY Monad._=<<_  _ = _=<<_  #-}
{-# DISPLAY Monad._>>_   _ = _>>_   #-}

monadAp : {M : ∀ {ℓ} → Set ℓ → Set ℓ} ⦃ _ : Functor M ⦄
  → (M (A → B) → ((A → B) → M B) → M B)
  → M (A → B) → M A → M B
monadAp _>>=_ mf mx = mf >>= λ f → fmap f mx
