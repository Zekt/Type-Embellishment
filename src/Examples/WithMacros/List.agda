{-# OPTIONS --safe --with-K #-}

module Examples.WithMacros.List where

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

open import Examples.WithMacros.Nat

--------
-- Connecting with the existing List datatype

instance

  ListC : Named (quote List) _
  unNamed ListC = genDataC ListD (genDataT ListD List)
    where ListD = genDataD List

  ListO : DataO (findDataD (quote List)) (findDataD (quote ℕ))
  ListO = record
    { level  = λ _ → tt
    ; applyL = λ (ℓ , _) → record
        { param  = λ _ → tt
        ; index  = λ _ _ → tt
        ; applyP = λ _ → ι ∷ ∺ (Δ[ _ ] ρ ι ι) ∷ ∺ [] } }

  ListFin : Finitary (findDataD (quote List))
  ListFin = [] ∷ (tt ∷ refl ∷ []) ∷ []

  ListS : SCᵈ (findDataD (quote List))
  ListS = record
    { El  = λ (A , _) → A
    ; pos = [] ∷ (true ∷ tt ∷ []) ∷ []
    ; coe = λ _ → lift tt ,ωω (refl ,ωω λ _ → lift tt) ,ωω lift tt }

--------
-- Connecting with the existing foldr function and deriving the fold fusion theorem

private
  foldListP : FoldP
  foldListP = fold-operator (quote List)

-- Generate foldList and its wrapper and connection, and then replace it with foldr
unquoteDecl foldList = defineFold foldListP foldList

instance
  foldrC = genFoldC' foldListP foldrT
    where
      foldrT : FoldT foldListP
      foldrT _ ((A , tt) , B , e , f , tt) = foldr e f

private
  foldr-fusionP : IndP
  foldr-fusionP = fold-fusion (quote List)

unquoteDecl foldr-fusion = defineInd foldr-fusionP foldr-fusion
-- foldr-fusion :
--   ∀ {ℓ' ℓ'' ℓ} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} (h : B → C)
--   {e : B} {f : A → B → B} {e' : C} {f' : A → C → C}
--   (he : h e ≡ e') (hf : (a : A) (b : B) (c : C) → h b ≡ c → h (f a b) ≡ f' a c)
--   (as : List A) → h (foldr e f as) ≡ foldr e' f' as
-- foldr-fusion h he hf []       = he
-- foldr-fusion h he hf (a ∷ as) = hf a _ _ (foldr-fusion h he hf as)

instance foldr-fusionC = genIndC foldr-fusionP foldr-fusion

--------
-- Algebraic ornamentation

private
  AlgListOD : DataOD (findDataD (quote List))
  AlgListOD = AlgOD foldListP

instance AlgListO = ⌈ AlgListOD ⌉ᵈ

unquoteDecl data AlgList constructor alg0 alg1 = defineByDataD ⌊ AlgListOD ⌋ᵈ AlgList (alg0 ∷ alg1 ∷ [])
--data AlgList {ℓ' ℓ} {A : Set ℓ} {B : Set ℓ'}
--  (e : B) (f : A → B → B) : B → Set (ℓ ⊔ ℓ') where
--  []  : AlgList e f e
--  _∷_ : (a : A) {b : B} → AlgList e f b → AlgList e f (f a b)

instance AlgListC = genDataC ⌊ AlgListOD ⌋ᵈ (genDataT ⌊ AlgListOD ⌋ᵈ AlgList)

private
  lengthP : FoldP
  lengthP = forget (quote List) (quote ℕ)

instance lengthC = genFoldC lengthP length

private
  VecOD : DataOD (findDataD (quote List))
  VecOD = AlgOD lengthP

instance VecO = ⌈ VecOD ⌉ᵈ

unquoteDecl data Vec constructor vec0 vec1 = defineByDataD ⌊ VecOD ⌋ᵈ Vec (vec0 ∷ vec1 ∷ [])
--data Vec (A : Set ℓ) : (n : ℕ) → Set ℓ where
--  []  : Vec A 0
--  _∷_ : (a : A) {n : ℕ} → Vec A n → Vec A (suc n)

instance

  VecC : Named (quote Vec) _
  unNamed VecC = genDataC ⌊ VecOD ⌋ᵈ (genDataT ⌊ VecOD ⌋ᵈ Vec)

  VecFin : Finitary ⌊ VecOD ⌋ᵈ
  VecFin = [] ∷ (tt ∷ tt ∷ refl ∷ []) ∷ []

private
  fromVecP : FoldP
  fromVecP = forget (quote Vec) (quote List)

unquoteDecl fromVec = defineFold fromVecP fromVec
-- fromVec : {A : Set ℓ} {n : ℕ} (v : Vec A n) → List A
-- fromVec []       = []
-- fromVec (a ∷ as) = a ∷ fromVec as

instance fromVecC = genFoldC fromVecP fromVec

private
  toVecP : IndP
  toVecP = remember (quote Vec)

unquoteDecl toVec = defineInd toVecP toVec
-- toVec :  {A : Set ℓ} (as : List A) → Vec A (length as)
-- toVec []       = []
-- toVec (a ∷ as) = a ∷ toVec as

instance toVecC = genIndC toVecP toVec

--private
--  from-toVecP : IndP
--  from-toVecP = forget-remember-inv (quote Vec) (quote List) (inl it)
--
--unquoteDecl from-toVec = defineInd from-toVecP from-toVec
-- from-toVec : {A : Set ℓ} (as : List A) → fromVec (toVec as) ≡ as
-- from-toVec []       = refl
-- from-toVec (a ∷ as) = cong (_∷_ a) (from-toVec as)

--instance from-toVecC = genIndC from-toVecP from-toVec

--private
--  to-fromVecP : IndP
--  to-fromVecP = remember-forget-inv (quote Vec) (quote List) (inl it)

--unquoteDecl to-fromVec = defineInd to-fromVecP to-fromVec
-- to-fromVec : {A : Set ℓ} {n : ℕ} (as : Vec A n) →
--              (length (fromVec as) , toVec (fromVec as)) ≡ ((n , as) ⦂ Σ ℕ (Vec A))
-- to-fromVec [] = refl
-- to-fromVec (a ∷ as) =
--   trans
--    (cong
--     (bimap (λ x₁ → x₁) (DataC.toN (findDataC (quote Vec))))
--     (cong (bimap (λ x₁ → x₁) inr)
--      (cong (bimap (λ x₁ → x₁) inl)
--       (cong (bimap (λ x₁ → x₁) (λ section → a , section))
--        (trans
--         (cong (λ p₁ → suc (fst p₁) , fst p₁ , snd p₁ , refl)
--          (to-fromVec as))
--         refl)))))
--    refl

--instance to-fromVecC = genIndC to-fromVecP to-fromVec

private
  LenOD : DataOD (findDataD (quote Vec))
  LenOD = AlgOD fromVecP

instance LenO = ⌈ LenOD ⌉ᵈ

unquoteDecl data Len constructor len0 len1 = defineByDataD ⌊ LenOD ⌋ᵈ Len (len0 ∷ len1 ∷ [])
--data Len {A : Set ℓ} : ℕ → List A → Set ℓ where
--  zero : Len 0 []
--  suc  : {a : A} {n : ℕ} {as : List A} → Len n as → Len (suc n) (a ∷ as)


instance
  LenC : Named (quote Len) _
  unNamed LenC = genDataC ⌊ LenOD ⌋ᵈ (genDataT ⌊ LenOD ⌋ᵈ Len)

private
  fromLenP : FoldP
  fromLenP = forget (quote Len) (quote Vec)

unquoteDecl fromLen = defineFold fromLenP fromLen
-- fromLen : {A : Set ℓ} {n : ℕ} {as : List A} → Len n as → Vec A n
-- fromLen  zero       = []
-- fromLen (suc {a} l) = a ∷ fromLen l

instance fromLenC = genFoldC fromLenP fromLen

private
  toLenP : IndP
  toLenP = remember (quote Len)

unquoteDecl toLen = defineInd toLenP toLen
-- toLen : {A : Set ℓ} {n : ℕ} (as : Vec A n) → Len n (fromVec as)
-- toLen []       = zero
-- toLen (a ∷ as) = suc (toLen as)

instance toLenC = genIndC toLenP toLen

--private
--  from-toLenP : IndP
--  from-toLenP = forget-remember-inv (quote Len) (quote Vec) (inl it)

--unquoteDecl from-toLen = defineInd from-toLenP from-toLen
-- from-toLen : {A : Set ℓ} {n : ℕ} (as : Vec A n) → fromLen (toLen as) ≡ as
-- from-toLen []       = refl
-- from-toLen (a ∷ as) = cong (_∷_ a) (from-toLen as)

--instance from-toLenC = genIndC from-toLenP from-toLen

--private
--  to-fromLenP : IndP
--  to-fromLenP = remember-forget-inv (quote Len) (quote Vec) (inl it)
--
--unquoteDecl to-fromLen = defineInd to-fromLenP to-fromLen
-- to-fromLen : {A : Set ℓ} {n : ℕ} {as : List A} (l : Len n as)
--            → (fromVec (fromLen l) , toLen (fromLen l))
--            ≡ ((as , l) ⦂ Σ[ as' ∈ List A ] Len n as')
-- to-fromLen                      zero   = refl
-- to-fromLen {n = suc n} {a ∷ _} (suc l) =
--   trans
--    (cong
--     (bimap (λ x → x) (DataC.toN (findDataC (quote Len))))
--     (cong (bimap (λ x → x) inr)
--      (cong (bimap (λ x → x) inl)
--       (cong (bimap (λ x → x) (λ section → a , section))
--        (cong (bimap (λ x → x) (λ section → n , section))
--         (trans
--          (cong (λ p → a ∷ fst p , fst p , snd p , refl) (to-fromLen l))
--          refl))))))
--    refl

--instance to-fromLenC = genIndC to-fromLenP to-fromLen

--------
-- All predicate

private
  ListPOD : DataOD (findDataD (quote List))
  ListPOD = PredOD (quote List)

instance ListPO = ⌈ ListPOD ⌉ᵈ

unquoteDecl data ListP constructor lp0 lp1 = defineByDataD ⌊ ListPOD ⌋ᵈ ListP (lp0 ∷ lp1 ∷ [])
--data ListP {ℓ' ℓ} {A : Set ℓ} (P : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
--  []      : ListP P
--  ⟨_,_⟩∷_ : (a : A) → P a → ListP P → ListP P

instance

  ListPC : Named (quote ListP) _
  unNamed ListPC = genDataC ⌊ ListPOD ⌋ᵈ (genDataT ⌊ ListPOD ⌋ᵈ ListP)

  ListPFin : Finitary ⌊ ListPOD ⌋ᵈ
  ListPFin = [] ∷ (tt ∷ tt ∷ refl ∷ []) ∷ []

private
  fromListPP : FoldP
  fromListPP = forget (quote ListP) (quote List)

unquoteDecl fromListP = defineFold fromListPP fromListP
-- fromListP : ∀ {ℓ' ℓ} {A : Set ℓ} {P : A → Set ℓ'} → ListP P → List A
-- fromListP []               = []
-- fromListP (⟨ a , p ⟩∷ aps) = a ∷ fromListP aps

instance fromListPC = genFoldC fromListPP fromListP

private
  ListAllOD : DataOD ⌊ ListPOD ⌋ᵈ
  ListAllOD = AllOD (quote List)

instance ListAllO = ⌈ ListAllOD ⌉ᵈ

unquoteDecl data ListAll constructor all0 all1 = defineByDataD ⌊ ListAllOD ⌋ᵈ ListAll (all0 ∷ all1 ∷ [])
--data ListAll {ℓ' ℓ} {A : Set ℓ} (P : A → Set ℓ') : List A → Set (ℓ ⊔ ℓ') where
--  []  : ListAll P []
--  _∷_ : {a : A} → P a → {as : List A} → ListAll P as → ListAll P (a ∷ as)

instance
  ListAllC : Named (quote ListAll) _
  unNamed ListAllC = genDataC ⌊ ListAllOD ⌋ᵈ ListAllT
    where ListAllT = genDataT ⌊ ListAllOD ⌋ᵈ ListAll

private
  fromAllP : FoldP
  fromAllP = forget (quote ListAll) (quote ListP)

unquoteDecl fromAll = defineFold fromAllP fromAll
-- fromAll : ∀ {ℓ' ℓ} {A : Set ℓ} {P : A → Set ℓ'} {as : List A} → ListAll P as → ListP P
-- fromAll []       = []
-- fromAll (p ∷ ps) = ⟨ _ , p ⟩∷ fromAll ps

instance fromAllC = genFoldC fromAllP fromAll

private
  toAllP : IndP
  toAllP = remember (quote ListAll)

unquoteDecl toAll = defineInd toAllP toAll
-- toAll : ∀ {ℓ' ℓ} {A : Set ℓ} {P : A → Set ℓ'} (aps : ListP P) → ListAll P (fromListP aps)
-- toAll []               = []
-- toAll (⟨ a , p ⟩∷ aps) = p ∷ toAll aps

instance toAllC = genIndC toAllP toAll

--private
--  from-toAllP : IndP
--  from-toAllP = forget-remember-inv (quote ListAll) (quote ListP) (inl it)
--
--unquoteDecl from-toAll = defineInd from-toAllP from-toAll
-- from-toAll : {ℓ' ℓ : Level} {A : Set ℓ} {P : A → Set ℓ'}
--              (aps : ListP P) → fromAll (toAll aps) ≡ aps
-- from-toAll [] = refl
-- from-toAll (⟨ a , p ⟩∷ aps) = cong (⟨_,_⟩∷_ a p) (from-toAll aps)

--instance from-toAllC = genIndC from-toAllP from-toAll

--private
--  to-fromAllP : IndP
--  to-fromAllP = remember-forget-inv (quote ListAll) (quote ListP) (inl it)
--
--unquoteDecl to-fromAll = defineInd to-fromAllP to-fromAll
-- to-fromAll : {ℓ' ℓ : Level} {A : Set ℓ} {P : A → Set ℓ'}
--              {as : List A} (all : ListAll P as)
--            → (fromListP (fromAll all) , toAll (fromAll all))
--            ≡ ((as , all) ⦂ Σ (List A) (ListAll P))
-- to-fromAll [] = refl
-- to-fromAll (p ∷ all) =
--   trans
--    (cong
--     (bimap (λ x₂ → x₂) (DataC.toN (findDataD (quote ListAll))))
--     (cong (bimap (λ x₂ → x₂) inr)
--      (cong (bimap (λ x₂ → x₂) inl)
--       (cong (bimap (λ x₂ → x₂) (λ section → a , section))
--        (cong (bimap (λ x₂ → x₂) (λ section → p , section))
--         (trans
--          (cong (λ p₁ → a ∷ fst p₁ , fst p₁ , snd p₁ , refl) (to-fromAll all))
--          refl))))))
--    refl

--instance to-fromAllC = genIndC to-fromAllP to-fromAll

--------
-- Any predicate

private
  ListAnyOD : DataOD (findDataD (quote ℕ))
  ListAnyOD = AnyOD (quote List)

instance ListAnyO = ⌈ ListAnyOD ⌉ᵈ

unquoteDecl data ListAny constructor any0 any1 = defineByDataD ⌊ ListAnyOD ⌋ᵈ ListAny (any0 ∷ any1 ∷ [])
--data ListAny {ℓ' ℓ} {A : Set ℓ} (P : A → Set ℓ') : List A → Set (ℓ ⊔ ℓ') where
--  here  : ∀ {a as} → P a → ListAny P (a ∷ as)
--  there : ∀ {a as} → ListAny P as → ListAny P (a ∷ as)

instance
  ListAnyC : Named (quote ListAny) _
  unNamed ListAnyC = genDataC ⌊ ListAnyOD ⌋ᵈ ListAnyT
    where ListAnyT = genDataT ⌊ ListAnyOD ⌋ᵈ ListAny

_∋_ : {A : Set ℓ} → List A → A → Set _
_∋_ {A = A} xs x = ListAny A (x ≡_) xs

private
  toℕP : FoldP
  toℕP = forget (quote ListAny) (quote ℕ)

unquoteDecl toℕ = defineFold toℕP toℕ
-- toℕ : ∀ {ℓ' ℓ} {A : Set ℓ} {P : A → Set ℓ'} {as : List A} → ListAny P as → ℕ
-- toℕ (here  p) = 0
-- toℕ (there i) = suc (toℕ i)

instance toℕC = genFoldC toℕP toℕ
