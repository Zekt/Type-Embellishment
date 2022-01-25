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
open import Generics.SimpleContainer.All
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

ListFin : Finitary ListD
ListFin _ = [] ∷ (tt ∷ refl ∷ []) ∷ []

ListS : SCᵈ ListD
ListS _ = record
  { El  = λ (A , _) → A
  ; pos = [] ∷ (true ∷ tt ∷ []) ∷ []
  ; coe = λ _ → lift tt ,ωω (refl ,ωω λ _ → lift tt) ,ωω lift tt }

--------
-- Connecting with the existing foldr function and deriving the fold fusion theorem

-- Generate foldList and its wrapper and connection, and then replace it with foldr
-- unquoteDecl foldList = defineFold (fold-operator ListC) foldList

foldrT : FoldT (fold-operator ListC)
foldrT _ ((A , tt) , B , e , f , tt) = foldr e f

foldrC = genFoldC' (fold-operator ListC) foldrT

-- unquoteDecl foldr-fusion = defineInd (fold-fusion ListC foldrC) foldr-fusion
foldr-fusion :
  {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
  (h : B → C) (e : B) (f : A → B → B) (e' : C) (f' : A → C → C)
  (he : h e ≡ e') (hf : (a : A) (b : B) (c : C) → h b ≡ c → h (f a b) ≡ f' a c)
  (as : List A) → h (foldr e f as) ≡ foldr e' f' as
foldr-fusion h e f e' f' he hf [] = he
foldr-fusion h e f e' f' he hf (a ∷ as) =
   hf a (foldr e f as) (foldr e' f' as) (foldr-fusion h e f e' f' he hf as)

foldr-fusionT : IndT (fold-fusion ListC foldrC)
foldr-fusionT _
  ((a , tt) , a₁ , a₂ , a₃ , (a₄ , a₅ , tt) , (a₆ , a₇ , tt) , a₈ , a₉ , tt) =
  foldr-fusion a₃ a₄ a₅ a₆ a₇ a₈ a₉

foldr-fusionC = genIndC' (fold-fusion ListC foldrC) foldr-fusionT

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

lengthC = genFoldC lengthP length

VecOD : DataOD ListD
VecOD = AlgOD lengthP

-- unquoteDecl data Vec constructor c0 c1 = defineByDataD ⌊ VecOD ⌋ᵈ Vec (c0 ∷ c1 ∷ [])
data Vec (A : Set ℓ) : (n : ℕ) → Set ℓ where
  []  : Vec A 0
  _∷_ : (a : A) {n : ℕ} → Vec A n → Vec A (suc n)

VecC = genDataC ⌊ VecOD ⌋ᵈ (genDataT ⌊ VecOD ⌋ᵈ Vec)

VecFin : Finitary ⌊ VecOD ⌋ᵈ
VecFin _ = [] ∷ (tt ∷ tt ∷ refl ∷ []) ∷ []

fromVecP : FoldP
fromVecP = forget VecC ListC ⌈ VecOD ⌉ᵈ

-- unquoteDecl fromVec = defineFold fromVecP fromVec
fromVec : {A : Set ℓ} {n : ℕ} (v : Vec A n) → List A
fromVec []       = []
fromVec (a ∷ as) = a ∷ fromVec as

fromVecC = genFoldC fromVecP fromVec

toVecP : IndP
toVecP = remember lengthC VecC

-- unquoteDecl toVec = defineInd toVecP toVec
toVec :  {A : Set ℓ} (as : List A) → Vec A (length as)  -- [WARNING] ‘length’ is manually un-normalised
toVec []       = []
toVec (a ∷ as) = a ∷ toVec as

toVecC = genIndC toVecP toVec

from-toVecP : IndP
from-toVecP = forget-remember-inv lengthC VecC fromVecC toVecC (inl ListFin)

-- unquoteDecl from-toVec = defineInd from-toVecP from-toVec
from-toVec : {A : Set ℓ} (as : List A) → fromVec (toVec as) ≡ as
from-toVec []       = refl
from-toVec (a ∷ as) = cong (λ n' → a ∷ n') (from-toVec as)

from-toVecC = genIndC from-toVecP from-toVec

to-fromVecP : IndP
to-fromVecP = remember-forget-inv lengthC VecC toVecC fromVecC (inl ListFin)

-- [FAIL] Cannot instantiate the metavariable…
-- unquoteDecl to-fromVec = defineInd to-fromVecP to-fromVec
to-fromVec : {A : Set ℓ} {n : ℕ} (as : Vec A n)
           → (length (fromVec as) , toVec (fromVec as))  -- [WARNING] ‘length’ is manually un-normalised
           ≡ ((n , as) ⦂ Σ[ n' ∈ ℕ ] Vec A n')           -- [FAIL] manual type annotation
to-fromVec []       = refl
to-fromVec (a ∷ as) =
  trans
   (cong
    (bimap (λ x → x) (DataC.toN VecC))  -- [FAIL] manually un-normalised
    (cong (bimap (λ x → x) inr)
     (cong (bimap (λ x → x) inl)
      (cong (bimap (λ x → x) (λ section → a , section))
       (trans
        (cong (λ p → suc (fst p) , fst p , snd p , refl) (to-fromVec as))
        refl)))))
   refl

to-fromVecC = genIndC to-fromVecP to-fromVec

LenOD : DataOD ⌊ VecOD ⌋ᵈ
LenOD = AlgOD fromVecP

-- unquoteDecl data Len constructor c0 c1 = defineByDataD ⌊ LenOD ⌋ᵈ Len (c0 ∷ c1 ∷ [])
data Len {A : Set ℓ} : ℕ → List A → Set ℓ where
  zero : Len 0 []
  suc  : {a : A} {n : ℕ} {as : List A} → Len n as → Len (suc n) (a ∷ as)

LenC = genDataC ⌊ LenOD ⌋ᵈ (genDataT ⌊ LenOD ⌋ᵈ Len)

fromLenP : FoldP
fromLenP = forget LenC VecC ⌈ LenOD ⌉ᵈ

-- unquoteDecl fromLen = defineFold fromLenP fromLen
fromLen : {A : Set ℓ} {n : ℕ} {as : List A} → Len n as → Vec A n
fromLen  zero       = []
fromLen (suc {a} l) = a ∷ fromLen l

fromLenC = genFoldC fromLenP fromLen

toLenP : IndP
toLenP = remember fromVecC LenC

-- unquoteDecl toLen = defineInd toLenP toLen
toLen : {A : Set ℓ} {n : ℕ} (as : Vec A n) → Len n (fromVec as)
toLen []       = zero
toLen (a ∷ as) = suc (toLen as)

toLenC = genIndC toLenP toLen

from-toLenP : IndP
from-toLenP = forget-remember-inv fromVecC LenC fromLenC toLenC (inl VecFin)

-- [FAIL] The case for the constructor refl is impossible…
-- unquoteDecl from-toLen = defineInd from-toLenP from-toLen
from-toLen : {A : Set ℓ} {n : ℕ} (as : Vec A n) → fromLen (toLen as) ≡ as
from-toLen             []       = refl
from-toLen {n = suc n} (a ∷ as) = cong (λ n' → a ∷ n') (from-toLen as)

from-toLenC = genIndC from-toLenP from-toLen

to-fromLenP : IndP
to-fromLenP = remember-forget-inv fromVecC LenC toLenC fromLenC (inl VecFin)

-- [FAIL] too slow; manually case-split and elaborate-and-give
-- unquoteDecl to-fromLen = defineInd to-fromLenP to-fromLen
to-fromLen : {A : Set ℓ} {n : ℕ} {as : List A} (l : Len n as)
           → (fromVec (fromLen l) , toLen (fromLen l))
           ≡ ((as , l) ⦂ Σ[ as' ∈ List A ] Len n as')  -- [FAIL] manual type annotation
to-fromLen                      zero   = refl
to-fromLen {n = suc n} {a ∷ _} (suc l) =
  trans
   (cong
    (bimap (λ x → x) (DataC.toN LenC))  -- [FAIL] manually un-normalised
    (cong (bimap (λ x → x) inr)
     (cong (bimap (λ x → x) inl)
      (cong (bimap (λ x → x) (λ section → a , section))
       (cong (bimap (λ x → x) (λ section → n , section))
        (trans
         (cong (λ p → a ∷ fst p , fst p , snd p , refl) (to-fromLen l))
         refl))))))
   refl

to-fromLenC = genIndC to-fromLenP to-fromLen

--------
-- All predicate

ListPOD : DataOD ListD
ListPOD = PredOD ListD ListS

-- unquoteDecl data ListP constructor c0 c1 = defineByDataD ⌊ ListPOD ⌋ᵈ ListP (c0 ∷ c1 ∷ [])
data ListP {A : Set ℓ} (P : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  []      : ListP P
  ⟨_,_⟩∷_ : (a : A) → P a → ListP P → ListP P

ListPT : DataT ⌊ ListPOD ⌋ᵈ
ListPT _ ((A , tt) , P , tt) tt = ListP P

ListPC = genDataC ⌊ ListPOD ⌋ᵈ ListPT

fromListPP : FoldP
fromListPP = forget ListPC ListC ⌈ ListPOD ⌉ᵈ

-- unquoteDecl fromListP = defineFold fromListPP fromListP
fromListP : {A : Set ℓ} {P : A → Set ℓ'} → ListP P → List A
fromListP []               = []
fromListP (⟨ a , p ⟩∷ aps) = a ∷ fromListP aps

fromListPT : FoldT fromListPP
fromListPT _ ((A , tt) , P , tt) = fromListP

fromListPC = genFoldC' fromListPP fromListPT

ListAllOD : DataOD ⌊ ListPOD ⌋ᵈ
ListAllOD = AllOD ListC ListS ListPC

-- unquoteDecl data ListAll constructor c0 c1 = defineByDataD ⌊ ListAllOD ⌋ᵈ ListAll (c0 ∷ c1 ∷ [])
data ListAll {A : Set ℓ} (P : A → Set ℓ') : List A → Set (ℓ ⊔ ℓ') where
  []  : ListAll P []
  _∷_ : {a : A} → P a → {as : List A} → ListAll P as → ListAll P (a ∷ as)

ListAllT : DataT ⌊ ListAllOD ⌋ᵈ
ListAllT _ ((A , tt) , P , tt) (tt , as , tt) = ListAll P as

ListAllC = genDataC ⌊ ListAllOD ⌋ᵈ ListAllT

fromAllP : FoldP
fromAllP = forget ListAllC ListPC ⌈ ListAllOD ⌉ᵈ

-- unquoteDecl fromAll = defineFold fromAllP fromAll
fromAll : {A : Set ℓ} {P : A → Set ℓ'} {as : List A} → ListAll P as → ListP P
fromAll []       = []
fromAll (p ∷ ps) = ⟨ _ , p ⟩∷ fromAll ps

fromAllT : FoldT fromAllP
fromAllT _ ((A , tt) , P , tt) = fromAll

fromAllC = genFoldC' fromAllP fromAllT

toAllP : IndP
toAllP = remember fromListPC ListAllC

-- unquoteDecl toAll = defineInd toAllP toAll
toAll : {A : Set ℓ} {P : A → Set ℓ'} (aps : ListP P) → ListAll P (fromListP aps)
toAll [] = []
toAll (⟨ a , p ⟩∷ aps) = p ∷ toAll aps

toAllT : IndT toAllP
toAllT _ ((A , tt) , P , tt) = toAll

toAllC = genIndC' toAllP toAllT

-- [TODO] inverse properties

--------
-- Any predicate

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

toℕC = genFoldC' (forget ListAnyC NatC ⌈ ListAnyOD ⌉ᵈ) toℕT
