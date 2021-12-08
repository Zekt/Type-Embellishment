{-# OPTIONS --safe #-}

module Generics.Safe.Description.FixedPoint where

open import Prelude
open import Generics.Safe.Description

data μ (D : DataD)
       {ℓs : DataD.Levels D}
       (ps : ⟦ PDataD.Param (DataD.applyL D ℓs) ⟧ᵗ)
     : ⟦ PDataD.Index (DataD.applyL D ℓs) ps ⟧ᵗ
     → Set (PDataD.level (DataD.applyL D ℓs)) where
  con : ∀ {is}
      → rewriteLevel (PDataD.level-pre-fixed-point (DataD.applyL D ℓs))
          (Lift (PDataD.level (DataD.applyL D ℓs)) (⟦ D ⟧ᵈ ℓs ps (μ D ps) is))
      → μ D ps is
