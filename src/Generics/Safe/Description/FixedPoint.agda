{-# OPTIONS --safe #-}

module Generics.Safe.Description.FixedPoint where

open import Prelude
open import Generics.Safe.Description

data μ (D : UPDataD)
       {ℓs : UPDataD.Levels D}
       (ps : ⟦ DataD.Param (UPDataD.Desc D ℓs) ⟧ᵗ)
     : ⟦ DataD.Index (UPDataD.Desc D ℓs) ps ⟧ᵗ
     → Set (DataD.level (UPDataD.Desc D ℓs)) where
  con : ∀ {is}
      → rewriteLevel (DataD.level-pre-fixed-point (UPDataD.Desc D ℓs))
          (Lift (DataD.level (UPDataD.Desc D ℓs)) (⟦ D ⟧ᵘᵖᵈ ℓs ps (μ D ps) is))
      → μ D ps is
