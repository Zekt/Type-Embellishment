{-# OPTIONS --safe --with-K --show-implicit #-}

module Examples.List where

open import Prelude

open import Generics.Telescope
open import Generics.Description
open import Generics.Recursion
open import Generics.Reflection

open import Generics.RecursionScheme
open import Generics.Ornament
open import Generics.Ornament.Description
open import Generics.Ornament.Algebraic
open import Generics.Ornament.Algebraic.Isomorphism
open import Generics.SimpleContainer
open import Generics.SimpleContainer.Any

open import Examples.Nat

--------
-- Connecting with the existing List datatype

ListD = genDataD List
ListC = genDataC ListD List  -- [FIXME]

ListO : DataO ListD NatD
ListO = record
  { level  = λ _ → tt
  ; applyL = λ (ℓ , _) → record
      { param  = λ _ → tt
      ; index  = λ _ _ → tt
      ; applyP = λ _ → ι ∷ ∺ (Δ[ _ ] ρ ι ι) ∷ ∺ [] } }

-- [TODO] binder syntax for ornaments

--------
-- Connecting with the existing foldr function and deriving the fold fusion theorem

-- [TODO] connecting with foldr

-- [TODO] fold fusion

--------
-- Algebraic ornamentation

-- [TODO] algebraically ornamented lists

lengthP : FoldP
lengthP = forget ListC NatC ListO

-- [TODO] connecting with the exisiting length function

VecOD : DataOD ListD
VecOD = AlgOD lengthP

VecD : DataD
VecD = ⌊ VecOD ⌋ᵈ

-- [TODO] print datatype definitions directly
-- (allow constructor overloading in unquoteDecl data?)

{- Generated by 'unquoteDecl data Vec constructor vnil vcons = defineByDataD VecD Vec (vnil ∷ vcons ∷ [])'

data Vec {ℓ : Level} (A : Set ℓ) : (n : ℕ) → Set ℓ where
  vnil : Vec A 0
  vcons : (a : A) (a₁ : ℕ) (v : Vec A a₁) → Vec A (suc a₁)

-}

data Vec (A : Set ℓ) : ℕ → Set ℓ where
  []  : Vec A 0
  _∷_ : (a : A) {n : ℕ} (as : Vec A n) → Vec A (suc n)

VecD′ = genDataD Vec
VecC = genDataC VecD Vec  -- [FIXME]

-- [TODO] generate datatype wrappers (allowing visibility changes)
-- [TODO] Add an option to choose if dot patterns are printed or not

fromVecP : FoldP
fromVecP = forget VecC ListC ⌈ VecOD ⌉ᵈ

-- [TODO] fromVec

-- [TODO] toVec

-- [TODO] fromVec and toVec form an isomorphism List A ≅ Σ[ n ∈ ℕ ] Vec A n

LenOD : DataOD VecD
LenOD = AlgOD fromVecP

LenD : DataD
LenD = ⌊ LenOD ⌋ᵈ

{- Generated by 'unquoteDecl data Len constructor lnil lcons = defineByDataD LenD Len (lnil ∷ lcons ∷ [])'

data Len {ℓ : Level} (A : Set ℓ) : (n : ℕ) (l : List A) → Set ℓ where
  lnil : Len A 0 []
  lcons : (a : A) (a₁ : ℕ) (a₂ : List A) (l : Len A a₁ a₂) →
        Len A (suc a₁) (a ∷ a₂)

-}

data Len {A : Set ℓ} : ℕ → List A → Set ℓ where
  nil  : Len 0 []
  cons : {a : A} {n : ℕ} {as : List A} {l : Len n as} → Len (suc n) (a ∷ as)

-- [TODO] connection & wrapper between LenD and Len

-- [TODO] Vec A n ≅ Σ[ as ∈ List A ] Len n as

--------
-- Any predicate for lists

ListS : SCᵈ ListD
ListS _ = record
  { El  = λ (A , _) → A
  ; pos = [] ∷ (true ∷ tt ∷ []) ∷ []
  ; coe = λ _ → lift tt ,ωω (refl ,ωω λ _ → lift tt) ,ωω lift tt }

ListAnyOD : DataOD NatD
ListAnyOD = AnyOD ListC ListS

open import Utils.Reflection
-- [FIXME]
unquoteDecl data ListAny constructor c₀ c₁ = defineByDataD ⌊ ListAnyOD ⌋ᵈ ListAny (c₀ ∷ c₁ ∷ [])

ListAnyT : DataT ⌊ ListAnyOD ⌋ᵈ
ListAnyT = (`uncurry ⌊ ListAnyOD ⌋ᵈ ListAny)

ListAnyC = genDataC ⌊ ListAnyOD ⌋ᵈ  ListAny 

_∋_ : {A : Set ℓ} → List A → A → Set ℓ
xs ∋ x = ListAny _ (x ≡_) xs  -- [FIXME]

-- [FIXME]
unquoteDecl toℕ = defineFold (forget ListAnyC NatC ⌈ ListAnyOD ⌉ᵈ) toℕ
