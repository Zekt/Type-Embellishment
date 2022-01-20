{-# OPTIONS --safe --without-K  #-}
open import Prelude

module Generics.Reflection.Uncurry where

open import Utils.Reflection
open import Utils.Error as Err

open import Generics.Telescope
open import Generics.Description

open import Generics.Reflection.Telescope

------------------------------------------------------------------------
-- Meta-level currying operations

uncurryDataD : (D : DataD) → Name → TC Term
uncurryDataD D d = let open DataD D in do
  `A ← getType d
  let ℓsΓΔ… , `A  = ⇑ `A ⦂ Telescope × Type
  
  let `ℓs   , ΓΔ… = splitAt #levels ℓsΓΔ…
  extendContextℓs #levels λ ℓs → let open PDataD (applyL ℓs) in do
    Γ , Δ… ← Param ⊆ᵗ? ΓΔ…
    extendCxtTel Param λ ps → let Index = Index ps in do
      Δ , _ ← Index ⊆ᵗ? Δ…

      let |Γ| = length Γ ; |Δ| = length Δ 
      
      let (_ , p₁) , (as₁ , _) = cxtToVars (|Γ| + |Δ|) (`tt , `tt) `ℓs
      (_ , p₂) , (as₂ , _) ← telToVars |Δ| (`tt , `tt) Param Γ
      (_ , p₃) , (as₃ , _) ← telToVars 0   (`tt , `tt) Index Δ

      return $ pat-lam₀ $
        ((`ℓs <> Γ <> Δ) ⊢ vArg p₁ ∷ vArg p₂ ∷ [ vArg p₃ ] `= def d (as₁ <> as₂ <> as₃))
        ∷ []

macro
  `uncurry : (D : DataD) → Name → Tactic
  `uncurry D d hole = do
    u ← uncurryDataD D d
    unify hole u
