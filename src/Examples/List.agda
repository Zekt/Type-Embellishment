{-# OPTIONS --safe --with-K #-}

module Examples.List where

open import Prelude
open import Generics.Telescope
open import Generics.Description
open import Generics.Recursion
open import Generics.RecursionScheme
open import Generics.Ornament
open import Generics.Ornament.Description
open import Generics.Ornament.Algebraic
open import Generics.Ornament.Algebraic.Isomorphism
open import Metalib.Datatype
open import Metalib.Connection
open import Metalib.Recursion
open import Utils.Reflection
open import Examples.Nat

ListD = genDataD List
ListC = genDataC ListD List

ListO : DataO ListD NatD
ListO = record
  { level  = λ _ → tt
  ; applyL = λ (ℓ , _) → record
      { param  = λ _ → tt
      ; index  = λ _ _ → tt
      ; applyP = λ (P , _) → ι ∷ ∺ (Δ λ _ → ρ ι ι) ∷ ∺ [] } }

-- length

VecOD : DataOD ListD
VecOD = AlgOD (forget ListC NatC ListO)

VecD : DataD
VecD = ⌊ VecOD ⌋ᵈ

-- [TODO] print datatype definitions directly
-- (allow constructor overloading in unquoteDecl data?)
-- unquoteDecl data Vec constructor vnil vcons = defineByDataD VecD Vec (vnil ∷ vcons ∷ [])

data Vec {ℓ : Level} (A : Set ℓ) : (n : ℕ) → Set ℓ where
  []  : Vec A 0
  _∷_ : (a : A) {a₁ : ℕ} (v : Vec A a₁) → Vec A (suc a₁)

-- [TODO] generate datatype wrappers (allowing visibility changes)
-- [TODO] Add an option to choose if dot patters are printed or not
VecC = genDataC VecD Vec

fromVecP : FoldP
fromVecP = forget VecC ListC ⌈ VecOD ⌉ᵈ

-- unquoteDecl foldVec = defineFold (fold-operator VecC) foldVec
unquoteDecl fromVec = defineFold fromVecP fromVec
-- fromVec : {ℓ : Level} {A : Set ℓ} {n : ℕ}
--   → Vec A n → List A
-- fromVec []       = []
-- fromVec (x ∷ xs) = x ∷ fromVec xs

LenOD : DataOD VecD
LenOD = AlgOD fromVecP

LenD : DataD
LenD = ⌊ LenOD ⌋ᵈ

-- unquoteDecl data Len constructor lnil lcons = defineByDataD LenD Len (lnil ∷ lcons ∷ [])

data Len {ℓ : Level} (A : Set ℓ) : (n : ℕ) (l : List A) → Set ℓ where
  lnil : Len A 0 []
  lcons : (a : A) (a₁ : ℕ) (a₂ : List A) (l : Len A a₁ a₂) →
        Len A (suc a₁) (a ∷ a₂)

LenC = genDataC LenD Len

foldLenP : FoldP
foldLenP = fold-operator LenC

unquoteDecl foldLen = defineFold foldLenP foldLen
