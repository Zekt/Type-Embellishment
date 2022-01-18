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

uncurryDataD : (D : DataD) → Term → TC Term
uncurryDataD D t = let open DataD D in do
  `A ← inferType t
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
--      dprint =<< printTelescope (`ℓs <> Γ <> Δ) (return [])
      
      return $ pat-lam₀ $
        ((`ℓs <> Γ <> Δ) ⊢ vArg p₁ ∷ vArg p₂ ∷ [ vArg p₃ ] `= (t `$$ as₁ `$$ as₂ `$$ as₃))
        ∷ []

macro
  `uncurry : (D : DataD) → Term → Tactic
  `uncurry D t hole = do
    u ← uncurryDataD D t
    unify hole u

-- private
--   L′ : (ℓs : Level ^ 1) → Set (fst ℓs) × ⊤ → ⊤ → Set (fst ℓs)
--   L′ = `uncurry 1 1 List

--   Nat′ : ⊤ → ⊤ → ⊤ → Set
--   Nat′ = `uncurry 0 0 ℕ
