{-# OPTIONS --safe --with-K #-}

module Examples.List where

open import Prelude

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
ListC = genDataC ListD (genDataT ListD List)

ListO : DataO ListD NatD
ListO = record
  { level  = λ _ → tt
  ; applyL = λ (ℓ , _) → record
      { param  = λ _ → tt
      ; index  = λ _ _ → tt
      ; applyP = λ _ → ι ∷ ∺ (Δ[ _ ] ρ ι ι) ∷ ∺ [] } }

--------
-- Connecting with the existing foldr function and deriving the fold fusion theorem

-- Generate foldList and its wrapper and connection, and then replace it with foldr
-- unquoteDecl foldList = defineFold (fold-operator ListC) foldList

foldrT : FoldT (fold-operator ListC)
foldrT _ ((A , tt) , B , e , f , tt) = foldr e f

foldrC = genFoldC (fold-operator ListC) foldrT

-- unquoteDecl foldr-fusion = defineInd (fold-fusion ListC foldrC) foldr-fusion
foldr-fusion :
  {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
  (h : B → C) (e : B) (f : A → B → B) (e' : C) (f' : A → C → C)
  (he : h e ≡ e') (hf : (a : A) (b : B) (c : C) → c ≡ h b → h (f a b) ≡ f' a c)
  (as : List A) → h (foldr e f as) ≡ foldr e' f' as
foldr-fusion h e f e' f' he hf [] = trans he refl
foldr-fusion h e f e' f' he hf (a ∷ as) =
  trans
   (hf a (foldr e f as) (foldr e' f' as) (sym (foldr-fusion h e f e' f' he hf as)))
   refl

foldr-fusionT : IndT (fold-fusion ListC foldrC)
foldr-fusionT _
  ((a , tt) , a₁ , a₂ , a₃ , (a₄ , a₅ , tt) , (a₆ , a₇ , tt) , a₈ , a₉ , tt) =
  foldr-fusion a₃ a₄ a₅ a₆ a₇ a₈ a₉

foldr-fusionC = genIndC (fold-fusion ListC foldrC) foldr-fusionT

--------
-- Algebraic ornamentation

-- unquoteDecl data AlgList constructor c0 c1 = defineByDataD ⌊ AlgOD (fold-operator ListC) ⌋ᵈ AlgList (c0 ∷ c1 ∷ [])
data AlgList {A : Set ℓ} {B : Set ℓ'} (e : B) (f : A → B → B) : B → Set (ℓ ⊔ ℓ') where
  []  : AlgList e f e
  _∷_ : (a : A) {b : B} → AlgList e f b → AlgList e f (f a b)

AlgListT : DataT ⌊ AlgOD (fold-operator ListC) ⌋ᵈ
AlgListT _ ((A , tt) , B , e , f , tt) (tt , b , tt) = AlgList e f b

AlgListC = genDataC ⌊ AlgOD (fold-operator ListC) ⌋ᵈ AlgListT

lengthP : FoldP
lengthP = forget ListC NatC ListO

lengthC = genFoldC lengthP (genFoldT lengthP length)

VecOD : DataOD ListD
VecOD = AlgOD lengthP

-- unquoteDecl data Vec constructor c0 c1 = defineByDataD ⌊ VecOD ⌋ᵈ Vec (c0 ∷ c1 ∷ [])
data Vec (A : Set ℓ) : (n : ℕ) → Set ℓ where
  []  : Vec A 0
  _∷_ : (a : A) {n : ℕ} → Vec A n → Vec A (suc n)

VecC = genDataC ⌊ VecOD ⌋ᵈ (genDataT ⌊ VecOD ⌋ᵈ Vec)

fromVecP : FoldP
fromVecP = forget VecC ListC ⌈ VecOD ⌉ᵈ

-- unquoteDecl fromVec = defineFold fromVecP fromVec
fromVec : {A : Set ℓ} {n : ℕ} (v : Vec A n) → List A
fromVec []       = []
fromVec (a ∷ as) = a ∷ fromVec as

fromVecC = genFoldC fromVecP (genFoldT fromVecP fromVec)

toVecP : IndP
toVecP = remember lengthC VecC

-- unquoteDecl toVec = defineInd toVecP toVec
toVec :  {A : Set ℓ} (as : List A) → Vec A (length as)
toVec []       = []
toVec (a ∷ as) = a ∷ toVec as

toVecC = genIndC toVecP (genIndT toVecP toVec)

-- [TODO] fromVec and toVec form an isomorphism List A ≅ Σ[ n ∈ ℕ ] Vec A n

LenOD : DataOD ⌊ VecOD ⌋ᵈ
LenOD = AlgOD fromVecP

-- unquoteDecl data Len constructor c0 c1 = defineByDataD ⌊ LenOD ⌋ᵈ Len (c0 ∷ c1 ∷ [])
data Len {A : Set ℓ} : ℕ → List A → Set ℓ where
  zero : Len 0 []
  suc  : {a : A} {n : ℕ} {as : List A} → Len n as → Len (suc n) (a ∷ as)

LenC = genDataC ⌊ LenOD ⌋ᵈ (genDataT ⌊ LenOD ⌋ᵈ Len)

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

-- unquoteDecl data ListAny constructor c0 c1 = defineByDataD ⌊ ListAnyOD ⌋ᵈ ListAny (c0 ∷ c1 ∷ [])
data ListAny {A : Set ℓ} (P : A → Set ℓ') : List A → Set (ℓ ⊔ ℓ') where
  zero : ∀ {a as} → P a → ListAny P (a ∷ as)
  suc  : ∀ {a as} → ListAny P as → ListAny P (a ∷ as)

ListAnyT : DataT ⌊ ListAnyOD ⌋ᵈ
ListAnyT _ ((A , tt) , P , tt) (tt , as , tt) = ListAny P as

ListAnyC = genDataC ⌊ ListAnyOD ⌋ᵈ ListAnyT

_∋_ : {A : Set ℓ} → List A → A → Set ℓ
xs ∋ x = ListAny (x ≡_) xs

-- unquoteDecl toℕ = defineFold (forget ListAnyC NatC ⌈ ListAnyOD ⌉ᵈ) toℕ
toℕ : {A : Set ℓ} {P : A → Set ℓ'} {as : List A} → ListAny P as → ℕ
toℕ (zero _) = 0
toℕ (suc  i) = suc (toℕ i)

toℕT : FoldT (forget ListAnyC NatC ⌈ ListAnyOD ⌉ᵈ)
toℕT _ ((A , tt) , P , tt) = toℕ

toℕC = genFoldC (forget ListAnyC NatC ⌈ ListAnyOD ⌉ᵈ) toℕT
