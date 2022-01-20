{-# OPTIONS --safe --with-K #-}

module Examples.BST where

open import Prelude hiding (lookupAny; _≤_)

open import Generics.Telescope
open import Generics.Description
open import Generics.Reflection

open import Generics.Ornament.Description
open import Generics.SimpleContainer
open import Generics.SimpleContainer.Any

open import Examples.Nat

variable
  h : ℕ

-- [FIXME] change to a non-parametric version
data B23Tree {Val : Set ℓ} (_≤_ : Val → Val → Set ℓ') : ℕ → Val → Val → Set (ℓ ⊔ ℓ') where

  node₀ : {l r : Val} → ⦃ l ≤ r ⦄
        → -----------------------
          B23Tree _≤_ 0 l r

  node₂ : {l r : Val} (x : Val)
        → B23Tree _≤_ h l x → B23Tree _≤_ h x r
        → ---------------------------------------------
          B23Tree _≤_ (suc h) l r

  node₃ : {l r : Val} (x y : Val)
        → B23Tree _≤_ h l x → B23Tree _≤_ h x y → B23Tree _≤_ h y r
        → ---------------------------------------------------------------------
          B23Tree _≤_ (suc h) l r

open import Utils.Reflection
B23TreeD = genDataD B23Tree
B23TreeC = genDataC B23TreeD B23Tree

B23TreeS : SCᵈ B23TreeD
B23TreeS ℓs = record
  { El  = fst
  ; pos = (false ∷ false ∷ false ∷ [])
        ∷ (false ∷ false ∷ false ∷ true ∷ tt ∷ tt ∷ [])
        ∷ (false ∷ false ∷ false ∷ true ∷ true ∷ tt ∷ tt ∷ tt ∷ []) ∷ []
  ; coe = λ _ → (λ a a₁ a₂ → lift tt)
            ,ωω (λ _ _ _ → refl ,ωω λ a → lift tt)
            ,ωω (λ _ _ _ → refl ,ωω λ _ → refl ,ωω λ _ → lift tt) ,ωω lift tt }

B23TreeAnyOD : DataOD NatD
B23TreeAnyOD = AnyOD B23TreeC B23TreeS

-- [TODO] B23TreeWP and B23TreeAll

-- [FIXME]
-- (check the number of constructors)
unquoteDecl data B23TreeAny constructor c0 c1 c2 c3 c4 c5 c6 c7 = defineByDataD ⌊ B23TreeAnyOD ⌋ᵈ B23TreeAny (c0 ∷ c1 ∷ c2 ∷ c3 ∷ c4 ∷ c5 ∷ c6 ∷ c7 ∷ [])

B23TreeAnyC = genDataC ⌊ B23TreeAnyOD ⌋ᵈ B23TreeAny

-- [FIXME]
unquoteDecl lookupAnyB23T = defineFold (lookupAny B23TreeC B23TreeS B23TreeAnyC) lookupAnyB23T
