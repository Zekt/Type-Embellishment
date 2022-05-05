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
ListFin = [] ∷ (tt ∷ refl ∷ []) ∷ []

ListS : SCᵈ ListD
ListS = record
  { El  = λ (A , _) → A
  ; pos = [] ∷ (true ∷ tt ∷ []) ∷ []
  ; coe = λ _ → lift tt ,ωω (refl ,ωω λ _ → lift tt) ,ωω lift tt }

--------
-- Connecting with the existing foldr function and deriving the fold fusion theorem

foldListP : FoldP
foldListP = fold-operator ListC

-- Generate foldList and its wrapper and connection, and then replace it with foldr
-- unquoteDecl foldList = defineFold foldListP foldList
foldList : {ℓ ℓ1 : Level} {p : Set ℓ1} {X : Set ℓ} (alg : X)
           (alg1 : (a : p) (z : X) → X) (l : List p) →
           X
foldList alg alg₁ [] = alg
foldList alg alg₁ (x ∷ xs) = alg₁ x (foldList alg alg₁ xs)


foldrC = genFoldC' foldListP foldrT
  where
    foldrT : FoldT foldListP
    foldrT _ ((A , tt) , B , e , f , tt) = foldr e f

foldr-fusionP : IndP
foldr-fusionP = fold-fusion ListC foldrC

-- unquoteDecl foldr-fusion = defineInd foldr-fusionP foldr-fusion
foldr-fusion :
  ∀ {ℓ' ℓ'' ℓ} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} (h : B → C)
  {e : B} {f : A → B → B} {e' : C} {f' : A → C → C}
  (he : h e ≡ e') (hf : (a : A) (b : B) (c : C) → h b ≡ c → h (f a b) ≡ f' a c)
  (as : List A) → h (foldr e f as) ≡ foldr e' f' as
foldr-fusion h he hf []       = he
foldr-fusion h he hf (a ∷ as) = hf a _ _ (foldr-fusion h he hf as)

foldr-fusionC = genIndC foldr-fusionP foldr-fusion

--------
-- Algebraic ornamentation

AlgListOD : DataOD ListD
AlgListOD = AlgOD foldListP

AlgListO = ⌈ AlgListOD ⌉ᵈ

-- unquoteDecl data AlgList constructor c0 c1 = defineByDataD ⌊ AlgListOD ⌋ᵈ AlgList (c0 ∷ c1 ∷ [])
data AlgList {ℓ' ℓ} {A : Set ℓ} {B : Set ℓ'}
  (e : B) (f : A → B → B) : B → Set (ℓ ⊔ ℓ') where
  []  : AlgList e f e
  _∷_ : (a : A) {b : B} → AlgList e f b → AlgList e f (f a b)

AlgListC = genDataC ⌊ AlgListOD ⌋ᵈ (genDataT ⌊ AlgListOD ⌋ᵈ AlgList)

lengthP : FoldP
lengthP = forget ListC NatC ListO -- (quote List) (quote ℕ)

lengthC = genFoldC lengthP length

VecOD : DataOD ListD
VecOD = AlgOD lengthP

VecO = ⌈ VecOD ⌉ᵈ

-- unquoteDecl data Vec constructor c0 c1 = defineByDataD ⌊ VecOD ⌋ᵈ Vec (c0 ∷ c1 ∷ [])
data Vec (A : Set ℓ) : (n : ℕ) → Set ℓ where
  []  : Vec A 0
  _∷_ : (a : A) {n : ℕ} → Vec A n → Vec A (suc n)

VecC = genDataC ⌊ VecOD ⌋ᵈ (genDataT ⌊ VecOD ⌋ᵈ Vec)

VecFin : Finitary ⌊ VecOD ⌋ᵈ
VecFin = [] ∷ (tt ∷ tt ∷ refl ∷ []) ∷ []

fromVecP : FoldP
fromVecP = forget VecC ListC VecO

-- unquoteDecl fromVec = defineFold fromVecP fromVec
fromVec : {A : Set ℓ} {n : ℕ} (v : Vec A n) → List A
fromVec []       = []
fromVec (a ∷ as) = a ∷ fromVec as

fromVecC = genFoldC fromVecP fromVec

toVecP : IndP
toVecP = remember lengthC VecC

-- unquoteDecl toVec = defineInd toVecP toVec
toVec :  {A : Set ℓ} (as : List A) → Vec A (length as)
toVec []       = []
toVec (a ∷ as) = a ∷ toVec as

toVecC = genIndC toVecP toVec

from-toVecP : IndP
from-toVecP = forget-remember-inv lengthC VecC fromVecC toVecC (inl ListFin) -- (quote Vec) (quote List) (inl it)

-- unquoteDecl from-toVec = defineInd from-toVecP from-toVec
from-toVec : {A : Set ℓ} (as : List A) → fromVec (toVec as) ≡ as
from-toVec []       = refl
from-toVec (a ∷ as) = cong (_∷_ a) (from-toVec as)

from-toVecC = genIndC from-toVecP from-toVec

-- private
to-fromVecP : IndP
to-fromVecP = remember-forget-inv lengthC VecC fromVecC toVecC (inl ListFin) -- (quote Vec) (quote List) (inl it)

-- unquoteDecl to-fromVec = defineInd to-fromVecP to-fromVec
to-fromVec : {A : Set ℓ} {n : ℕ} (as : Vec A n) →
             (length (fromVec as) , toVec (fromVec as)) ≡ ((n , as) ⦂ Σ ℕ (Vec A))
to-fromVec [] = refl
to-fromVec (a ∷ as) =
  trans
   (cong
    (bimap (λ x₁ → x₁) (DataC.toN VecC))
    (cong (bimap (λ x₁ → x₁) inr)
     (cong (bimap (λ x₁ → x₁) inl)
      (cong (bimap (λ x₁ → x₁) (λ section → a , section))
       (trans
        (cong (λ p₁ → suc (fst p₁) , fst p₁ , snd p₁ , refl)
         (to-fromVec as))
        refl)))))
   refl

to-fromVecC = genIndC to-fromVecP to-fromVec

LenOD : DataOD ⌊ VecOD ⌋ᵈ -- (findDataD (quote Vec))
LenOD = AlgOD fromVecP

LenO = ⌈ LenOD ⌉ᵈ

-- unquoteDecl data Len constructor c0 c1 = defineByDataD ⌊ LenOD ⌋ᵈ Len (c0 ∷ c1 ∷ [])
data Len {A : Set ℓ} : ℕ → List A → Set ℓ where
  zero : Len 0 []
  suc  : {a : A} {n : ℕ} {as : List A} → Len n as → Len (suc n) (a ∷ as)

LenC = genDataC ⌊ LenOD ⌋ᵈ (genDataT ⌊ LenOD ⌋ᵈ Len)

fromLenP : FoldP
fromLenP = forget LenC VecC LenO -- (quote Len) (quote Vec)

-- unquoteDecl fromLen = defineFold fromLenP fromLen
fromLen : {A : Set ℓ} {n : ℕ} {as : List A} → Len n as → Vec A n
fromLen  zero       = []
fromLen (suc {a} l) = a ∷ fromLen l

fromLenC = genFoldC fromLenP fromLen

toLenP : IndP
toLenP = remember fromVecC LenC -- (quote Len)

-- unquoteDecl toLen = defineInd toLenP toLen
toLen : {A : Set ℓ} {n : ℕ} (as : Vec A n) → Len n (fromVec as)
toLen []       = zero
toLen (a ∷ as) = suc (toLen as)

toLenC = genIndC toLenP toLen

from-toLenP : IndP
from-toLenP = forget-remember-inv fromVecC LenC fromLenC toLenC (inl VecFin) -- (quote Len) (quote Vec) (inl it)

-- unquoteDecl from-toLen = defineInd from-toLenP from-toLen
from-toLen : {A : Set ℓ} {n : ℕ} (as : Vec A n) → fromLen (toLen as) ≡ as
from-toLen []       = refl
from-toLen (a ∷ as) = cong (_∷_ a) (from-toLen as)

from-toLenC = genIndC from-toLenP from-toLen

to-fromLenP : IndP
to-fromLenP = remember-forget-inv fromVecC LenC fromLenC toLenC (inl VecFin) -- (quote Len) (quote Vec) (inl it)

-- unquoteDecl to-fromLen = defineInd to-fromLenP to-fromLen
to-fromLen : {A : Set ℓ} {n : ℕ} {as : List A} (l : Len n as)
           → (fromVec (fromLen l) , toLen (fromLen l))
           ≡ ((as , l) ⦂ Σ[ as' ∈ List A ] Len n as')
to-fromLen                      zero   = refl
to-fromLen {n = suc n} {a ∷ _} (suc l) =
  trans
   (cong
    (bimap (λ x → x) (DataC.toN LenC))
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

ListPOD : DataOD ListD -- (findDataD (quote List))
ListPOD = PredOD ListC ListS -- (quote List)

ListPO = ⌈ ListPOD ⌉ᵈ

-- unquoteDecl data ListP constructor c0 c1 = defineByDataD ⌊ ListPOD ⌋ᵈ ListP (c0 ∷ c1 ∷ [])
data ListP {ℓ' ℓ} {A : Set ℓ} (P : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  []      : ListP P
  ⟨_,_⟩∷_ : (a : A) → P a → ListP P → ListP P

-- instance

ListPC = genDataC ⌊ ListPOD ⌋ᵈ (genDataT ⌊ ListPOD ⌋ᵈ ListP)

ListPFin : Finitary ⌊ ListPOD ⌋ᵈ
ListPFin = [] ∷ (tt ∷ tt ∷ refl ∷ []) ∷ []

fromListPP : FoldP
fromListPP = forget ListPC ListC ListPO -- (quote ListP) (quote List)

-- unquoteDecl fromListP = defineFold fromListPP fromListP
fromListP : ∀ {ℓ' ℓ} {A : Set ℓ} {P : A → Set ℓ'} → ListP P → List A
fromListP []               = []
fromListP (⟨ a , p ⟩∷ aps) = a ∷ fromListP aps

fromListPC = genFoldC fromListPP fromListP

ListAllOD : DataOD ⌊ ListPOD ⌋ᵈ
ListAllOD = AllOD ListC ListS ListPC -- (quote List)

ListAllO = ⌈ ListAllOD ⌉ᵈ

-- unquoteDecl data ListAll constructor c0 c1 = defineByDataD ⌊ ListAllOD ⌋ᵈ ListAll (c0 ∷ c1 ∷ [])
data ListAll {ℓ' ℓ} {A : Set ℓ} (P : A → Set ℓ') : List A → Set (ℓ ⊔ ℓ') where
  []  : ListAll P []
  _∷_ : {a : A} → P a → {as : List A} → ListAll P as → ListAll P (a ∷ as)

-- instance
ListAllC = genDataC ⌊ ListAllOD ⌋ᵈ ListAllT
  where ListAllT = genDataT ⌊ ListAllOD ⌋ᵈ ListAll

-- private
fromAllP : FoldP
fromAllP = forget ListAllC ListPC ListAllO -- (quote ListAll) (quote ListP)

-- unquoteDecl fromAll = defineFold fromAllP fromAll
fromAll : ∀ {ℓ' ℓ} {A : Set ℓ} {P : A → Set ℓ'} {as : List A} → ListAll P as → ListP P
fromAll []       = []
fromAll (p ∷ ps) = ⟨ _ , p ⟩∷ fromAll ps

fromAllC = genFoldC fromAllP fromAll

-- private
toAllP : IndP
toAllP = remember fromListPC ListAllC -- (quote ListAll)

-- unquoteDecl toAll = defineInd toAllP toAll
toAll : ∀ {ℓ' ℓ} {A : Set ℓ} {P : A → Set ℓ'} (aps : ListP P) → ListAll P (fromListP aps)
toAll []               = []
toAll (⟨ a , p ⟩∷ aps) = p ∷ toAll aps

toAllC = genIndC toAllP toAll

-- private
from-toAllP : IndP
from-toAllP = forget-remember-inv fromListPC ListAllC fromAllC toAllC (inl ListPFin) -- (quote ListAll) (quote ListP) (inl it)

-- unquoteDecl from-toAll = defineInd from-toAllP from-toAll
from-toAll : {ℓ' ℓ : Level} {A : Set ℓ} {P : A → Set ℓ'}
             (aps : ListP P) → fromAll (toAll aps) ≡ aps
from-toAll [] = refl
from-toAll (⟨ a , p ⟩∷ aps) = cong (⟨_,_⟩∷_ a p) (from-toAll aps)

from-toAllC = genIndC from-toAllP from-toAll

to-fromAllP : IndP
to-fromAllP = remember-forget-inv fromListPC ListAllC fromAllC toAllC (inl ListPFin) -- (quote ListAll) (quote ListP) (inl it)

-- unquoteDecl to-fromAll = defineInd to-fromAllP to-fromAll
to-fromAll : {ℓ' ℓ : Level} {A : Set ℓ} {P : A → Set ℓ'}
             {as : List A} (all : ListAll P as)
           → (fromListP (fromAll all) , toAll (fromAll all))
           ≡ ((as , all) ⦂ Σ (List A) (ListAll P))
to-fromAll [] = refl
to-fromAll (p ∷ all) =
  trans
   (cong
    (bimap (λ x₂ → x₂) (DataC.toN ListAllC))
    (cong (bimap (λ x₂ → x₂) inr)
     (cong (bimap (λ x₂ → x₂) inl)
      (cong (bimap (λ x₂ → x₂) (λ section → _ , section))
       (cong (bimap (λ x₂ → x₂) (λ section → p , section))
        (trans
         (cong (λ p₁ → _ ∷ fst p₁ , fst p₁ , snd p₁ , refl) (to-fromAll all))
         refl))))))
   refl

to-fromAllC = genIndC to-fromAllP to-fromAll

--------
-- Any predicate

ListAnyOD : DataOD NatD -- (findDataD (quote ℕ))
ListAnyOD = AnyOD ListC ListS -- (quote List)

ListAnyO = ⌈ ListAnyOD ⌉ᵈ

-- unquoteDecl data ListAny constructor c0 c1 = defineByDataD ⌊ ListAnyOD ⌋ᵈ ListAny (c0 ∷ c1 ∷ [])
data ListAny {ℓ' ℓ} {A : Set ℓ} (P : A → Set ℓ') : List A → Set (ℓ ⊔ ℓ') where
  here  : ∀ {a as} → P a → ListAny P (a ∷ as)
  there : ∀ {a as} → ListAny P as → ListAny P (a ∷ as)

ListAnyC = genDataC ⌊ ListAnyOD ⌋ᵈ ListAnyT
  where ListAnyT = genDataT ⌊ ListAnyOD ⌋ᵈ ListAny

_∋_ : {A : Set ℓ} → List A → A → Set ℓ
xs ∋ x = ListAny (x ≡_) xs

toℕP : FoldP
toℕP = forget ListAnyC NatC ListAnyO -- (quote ListAny) (quote ℕ)

-- unquoteDecl toℕ = defineFold toℕP toℕ
toℕ : ∀ {ℓ' ℓ} {A : Set ℓ} {P : A → Set ℓ'} {as : List A} → ListAny P as → ℕ
toℕ (here  p) = 0
toℕ (there i) = suc (toℕ i)

toℕC = genFoldC toℕP toℕ
