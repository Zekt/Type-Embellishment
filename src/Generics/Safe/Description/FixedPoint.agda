{-# OPTIONS --safe --without-K #-}

module Generics.Safe.Description.FixedPoint where

open import Prelude
open import Generics.Safe.Telescope
open import Generics.Safe.Description

data μ (D : DataD)
       (ℓs : DataD.Levels D)
       (ps : ⟦ PDataD.Param (DataD.applyL D ℓs) ⟧ᵇᵗ)
     : let Dᵖ = DataD.applyL D ℓs
       in  ⟦ PDataD.Index Dᵖ ps ⟧ᵇᵗ → Set (PDataD.dlevel Dᵖ) where
  con : let Dᵖ = DataD.applyL D ℓs in ∀ {is}
      → rewriteLevel (PDataD.level-pre-fixed-point Dᵖ)
          (Lift (PDataD.dlevel Dᵖ) (⟦ D ⟧ᵈ (μ D ℓs ps) is))
      → μ D ℓs ps is
