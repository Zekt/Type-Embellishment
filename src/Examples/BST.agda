{-# OPTIONS --safe --with-K #-}

open import Prelude hiding (_≤_)

module Examples.BST {ℓ ℓ'} (Val : Set ℓ) (_≤_ : Val → Val → Set ℓ') where

open import Generics.Telescope
open import Generics.Description
open import Generics.SimpleContainer

variable
  h   : ℕ
  l r : Val

data B23Tree : ℕ → Val → Val → Set (ℓ ⊔ ℓ') where

  node₀ : ⦃ l ≤ r ⦄
        → -------------
          B23Tree 0 l r

  node₂ : (x : Val)
        → B23Tree h l x → B23Tree h x r
        → -----------------------------
          B23Tree (suc h) l r

  node₃ : (x y : Val)
        → B23Tree h l x → B23Tree h x y → B23Tree h y r
        → ---------------------------------------------
          B23Tree (suc h) l r
