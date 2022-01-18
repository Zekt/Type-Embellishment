{-# OPTIONS --safe --with-K #-}

open import Prelude hiding (lookupAny; _≤_)

module Examples.BST where

open import Generics.Telescope
open import Generics.Description
open import Generics.Ornament.Description
open import Generics.SimpleContainer
open import Generics.SimpleContainer.Any
open import Generics.RecursionScheme

open import Generics.Reflection
open import Utils.Reflection hiding (Term)
open import Examples.Nat

variable
  h   : ℕ

data B23Tree {ℓ ℓ'} (Val : Set ℓ) (_≤_ : Val → Val → Set ℓ') : ℕ → Val → Val → Set (ℓ ⊔ ℓ') where

  node₀ : {l r : Val} → ⦃ l ≤ r ⦄
        → -------------
          B23Tree Val _≤_ 0 l r

  node₂ : {l r : Val} (x : Val)
        → B23Tree Val _≤_ h l x → B23Tree Val _≤_ h x r
        → -----------------------------
          B23Tree Val _≤_ (suc h) l r

  node₃ : {l r : Val} (x y : Val)
        → B23Tree Val _≤_ h l x → B23Tree Val _≤_ h x y → B23Tree Val _≤_ h y r
        → ---------------------------------------------
          B23Tree Val _≤_ (suc h) l r

B23TreeD = genDataD B23Tree
B23TreeC = genDataC B23TreeD B23Tree

B23TreeS : SCᵈ B23TreeD
B23TreeS ℓs = record
  { El = fst
  ; pos = (false ∷ false ∷ false ∷ [])
        ∷ (false ∷ false ∷ false ∷ true ∷ tt ∷ tt ∷ [])
        ∷ (false ∷ false ∷ false ∷ true ∷ true ∷ tt ∷ tt ∷ tt ∷ []) ∷ []
  ; coe = λ _ → (λ a a₁ a₂ → lift tt)
            ,ωω (λ _ _ _ → refl ,ωω λ a → lift tt)
            ,ωω (λ _ _ _ → refl ,ωω λ _ → refl ,ωω λ _ → lift tt) ,ωω lift tt }

AnyB23TreeOD : DataOD NatD
AnyB23TreeOD = AnyOD B23TreeC B23TreeS

-- [FIXME] check the number of constructors
unquoteDecl data AnyB23Tree constructor con0 con1 con2 con3 con4 con5 con6 con7 = defineByDataD ⌊ AnyB23TreeOD ⌋ᵈ AnyB23Tree (con0 ∷ con1 ∷ con2 ∷ con3 ∷ con4 ∷ con5 ∷ con6 ∷ con7 ∷ [])
AnyB23TreeC = genDataC ⌊ AnyB23TreeOD ⌋ᵈ AnyB23Tree

-- [FAIL] too slow
-- unquoteDecl foldAnyB23T = defineFold (fold-operator AnyB23TreeC) foldAnyB23T

unquoteDecl lookupAnyB23T = defineFold (lookupAny B23TreeC B23TreeS AnyB23TreeC) lookupAnyB23T
