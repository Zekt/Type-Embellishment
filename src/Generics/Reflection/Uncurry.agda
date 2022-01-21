{-# OPTIONS --safe --without-K #-}
open import Prelude

module Generics.Reflection.Uncurry where

open import Utils.Reflection
open import Utils.Error as Err

open import Generics.Telescope
open import Generics.Recursion
open import Generics.Description

open import Generics.Reflection.Telescope

------------------------------------------------------------------------
-- Meta-level currying operations

uncurryDataD : (D : DataD) → Name → TC Term
uncurryDataD D d = let open DataD D in do
  `A ← getType d
  
  let `ℓsΓΔ⋯ , _  = ⇑ `A ⦂ Telescope × Type
  let `ℓs   , ΓΔ⋯ = splitAt #levels `ℓsΓΔ⋯

  extendContextℓs #levels λ ℓs → let open PDataD (applyL ℓs) in do
    Γ , Δ⋯ ← Param ⊆ᵗ? ΓΔ⋯
    extendCxtTel Param λ ps → let Index = Index ps in do
      Δ , _ ← Index ⊆ᵗ? Δ⋯

      let |Γ| = length Γ ; |Δ| = length Δ 
      
      let (_ , p₁) , (as₁ , _) = cxtToVars (|Γ| + |Δ|) (`tt , `tt) `ℓs
      (_ , p₂) , (as₂ , _) ← telToVars |Δ| (`tt , `tt) Param Γ
      (_ , p₃) , (as₃ , _) ← telToVars 0   (`tt , `tt) Index Δ

      return $ pat-lam₀ $
        ((`ℓs <> Γ <> Δ) ⊢ vArg p₁ ∷ vArg p₂ ∷ [ vArg p₃ ] `= def d (as₁ <> as₂ <> as₃))
        ∷ []

uncurryFoldP : (P : FoldP) → Name → TC Term
uncurryFoldP P d = let open FoldP P in do
  `A ← getType d
  let `ℓsΓΔ⋯ , _   = ⇑ `A ⦂ Telescope × Type
  let `ℓs    , ΓΔ⋯ = splitAt #levels `ℓsΓΔ⋯
  extendContextℓs #levels λ ℓs → do
    let PsTel = Param ℓs
    Γ , Δ⋯ ← PsTel ⊆ᵗ? ΓΔ⋯
    extendCxtTel PsTel λ ps → do
      let Index = PDataD.Index (DataD.applyL Desc (level ℓs)) (param ps)
      Δ , _ ← Index ⊆ᵗ? Δ⋯ 

      let |Γ| = length Γ ; |Δ| = length Δ
      let ((_ , p₁) , as₁ , _) = cxtToVars (|Γ| + |Δ|) (`tt , `tt) `ℓs
      (_ , p₂) , (as₂ , _) ← telToVars |Δ| (`tt , `tt) PsTel Γ
      (_ , p₃) , (as₃ , _) ← telToVars 0 (`tt , `tt) Index Δ
      return $ pat-lam₀ $
        ((forgetTypes $ `ℓs <> Γ <> Δ) ⊢ vArg p₁ ∷ vArg p₂ ∷ hArg p₃ ∷ [] `= def d (as₁ <> as₂ <> as₃) )
        ∷ []

macro
  genDataT : (D : DataD) → Name → Tactic
  genDataT D d hole = do
    `D ← quoteωTC D
    checkType hole (def₁ (quote DataT) `D)
    uncurryDataD D d >>= unify hole

  genFoldGT : (P : FoldP) → Name → Tactic
  genFoldGT P d hole = do
    `P ← quoteωTC P
    checkType hole (def₁ (quote FoldGT) `P)
    uncurryFoldP P d >>= unify hole

