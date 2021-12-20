{-# OPTIONS --safe --without-K #-}
open import Prelude

module Utils.Reflection.Term where

open import Utils.Reflection.Core

prefixToType : Telescope → Type → Type
prefixToType []              `B = `B
prefixToType ((s , `A) ∷ `T) `B = `Π[ s ∶ `A ] prefixToType `T `B

prefixToTerm : Telescope → Term → Term
prefixToTerm []              `t = `t
prefixToTerm ((s , `A) ∷ `T) `t =
  lam (getVisibility `A) (abs s (prefixToTerm `T `t))

levels : ℕ → Telescope
levels zero    = []
levels (suc n) = ("_" , hArg `Level) ∷ levels n

private
  -- Assumption: The argument is a valid type.
  ΠToTelescope : Type → Telescope × Type
  ΠToTelescope (pi a (abs s b)) = let T , A = ΠToTelescope b in (s , a) ∷ T , A
  ΠToTelescope t                = [] , t

  TelescopeToΠ : Type → Telescope → Type
  TelescopeToΠ `B []             = `B
  TelescopeToΠ `B ((s , `A) ∷ T) = `Π[ s ∶ `A ] TelescopeToΠ `B T
instance
  TelescopeToContext : Coercion' Telescope Context
  ⇑_ ⦃ TelescopeToContext ⦄ = map snd

  TypeToTelescope : Coercion' Type (Telescope × Type)
  ⇑_ ⦃ TypeToTelescope ⦄ = ΠToTelescope

  TelescopeToType : Coercion' (Telescope × Type) Type
  ⇑_ ⦃ TelescopeToType ⦄ (T , `A) = TelescopeToΠ `A T

