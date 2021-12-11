{-# OPTIONS --safe --without-K #-}

module Generics.Safe.Description.FixedPoint where

open import Prelude
open import Generics.Safe.Description

data μ (D : DataD)
       {ℓs : DataD.Levels D}
       (ps : ⟦ PDataD.Param (DataD.applyL D ℓs) ⟧ᵗ)
     : let Dᵖ = DataD.applyL D ℓs
       in  ⟦ PDataD.Index Dᵖ ps ⟧ᵗ → Set (PDataD.dlevel Dᵖ ⊔ PDataD.ilevel Dᵖ) where
  con : let Dᵖ = DataD.applyL D ℓs in ∀ {is}
      → rewriteLevel (PDataD.level-pre-fixed-point Dᵖ)
          (Lift (PDataD.dlevel Dᵖ ⊔ PDataD.ilevel Dᵖ) (⟦ D ⟧ᵈ ℓs ps (μ D ps) is))
      → μ D ps is
