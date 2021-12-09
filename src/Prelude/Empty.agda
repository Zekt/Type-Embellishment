{-# OPTIONS --without-K --safe #-}
module Prelude.Empty where

data ⊥ : Set where

⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
⊥-elim ()
