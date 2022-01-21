{-# OPTIONS --safe --with-K #-}
module Tests.SCMTest where

open import Prelude
open import Generics.Telescope
open import Generics.Description
open import Generics.Description.FixedPoint
open import Generics.Algebra
open import Generics.Recursion
open import Generics.RecursionScheme

---- List 

-- META
ListD : DataD
ListD = record
  { #levels = 1
  ; applyL  = λ ℓs → let (ℓ , _) = ℓs in record
      { alevel = ℓ
--      ; level-inequality = refl
      ; Param  = [ A ∶ Set ℓ ] []
      ; Index  = λ _ → []
      ; applyP = λ ps → let (A , _) = ps
                        in (ι tt)
                         ∷ (σ A λ _ → ρ (ι tt) (ι tt))
                         ∷ [] } }

-- META
List-wrapper : DataT ListD
List-wrapper (ℓ , _) (A , _) _ = List A

-- META
ListC : DataC ListD List-wrapper
ListC = record
  { toN   = λ { (inl                refl  ) → []
              ; (inr (inl (a , as , refl))) → a ∷ as }
  ; fromN = λ { []       → inl                refl
              ; (a ∷ as) → inr (inl (a , as , refl)) }
  ; fromN-toN = λ { (inl                refl  ) → refl
                  ; (inr (inl (a , as , refl))) → refl }
  ; toN-fromN = λ { []       → refl
                  ; (a ∷ as) → refl } }

-- USER (specialising a generic library component)
foldListP : FoldP
foldListP = fold-operator ListC

-- META

foldList : {ℓs : (Level × Level × ⊤)} 
         → {A : Set (fst ℓs)} {X : Set (fst (snd ℓs))} 
         → X → (A → X → X) → List A → X
foldList e f [] = e
foldList e f (x ∷ xs) = f x (foldList e f xs)

foldList-wrapper : FoldT foldListP
foldList-wrapper _ ((A , tt) , X , e , f , tt) = foldList e f 

foldList-is-fold : FoldC foldListP foldList-wrapper
FoldC.equation foldList-is-fold (inl refl) = refl
FoldC.equation foldList-is-fold (inr (inl (x , xs , refl))) = refl

---- Internally & Enternally Labelled Binary Tree

data IETree {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  tip : A → IETree A B
  bin : B → IETree A B → IETree A B → IETree A B

-- META

IETreeD : DataD
IETreeD = record
  { #levels = 2
  ; applyL  = λ ℓs → let (ℓ , ℓ' , _) = ℓs in record
      { alevel = ℓ ⊔ ℓ'
 --     ; level-inequality = refl
      ; Param  = [ A ∶ Set ℓ ] [ B ∶ Set ℓ' ] []
      ; Index  = λ _ → []
      ; applyP = λ ps → let (A , B , _) = ps
                        in (σ A λ _ → ι tt)
                         ∷ (σ B λ _ → ρ (ι tt) (ρ (ι tt) (ι tt)))
                         ∷ [] } }

IETree-wrapper : DataT IETreeD
IETree-wrapper (ℓ , ℓ' , _) (A , B , _) _ = IETree A B

IETreeC : DataC IETreeD IETree-wrapper
IETreeC = record
  { toN   = λ { (inl (x , refl)) → tip x
              ; (inr (inl (y , t , u , refl))) → bin y t u }
  ; fromN = λ { (tip x) → inl (x , refl)
              ; (bin y t u) → inr (inl (y , t , u , refl))}
  ; fromN-toN = λ { (inl (x , refl)) → refl
                  ; (inr (inl (y , t , u , refl))) → refl }
  ; toN-fromN = λ { (tip x) → refl
                  ; (bin y t u) → refl} }

-- USER

foldIEP : FoldP
foldIEP = fold-operator IETreeC

-- META

foldIE : {ℓs : (Level × Level × Level × ⊤)}  
       → let (ℓ , ℓ₁ , ℓ₂ , _) = ℓs
         in {A : Set ℓ₁} {B : Set ℓ₂} {X : Set ℓ} 
            → (A → X) → (B → X → X → X) → IETree A B → X
foldIE g f (tip x) = g x
foldIE g f (bin y t u) = f y (foldIE g f t) (foldIE g f u)

foldIE-wrapper : FoldT foldIEP
foldIE-wrapper _ ((A , B , _) , X , g , f , tt) = foldIE g f

foldIE-is-fold : FoldC foldIEP foldIE-wrapper
FoldC.equation foldIE-is-fold (inl (x , refl)) = refl
FoldC.equation foldIE-is-fold (inr (inl (y , t , u , refl))) = refl


---- Hand-Crafted Vectors

-- META
VecD : DataD
VecD = record
  { #levels = 1
  ; applyL  = λ ℓs → let (ℓ , _) = ℓs in record
      { alevel = ℓ
--      ; level-inequality = refl
      ; Param  = [ A ∶ Set ℓ ] []
      ; Index  = λ _ → ℕ ∷ (λ _ → [])
      ; applyP = λ ps → let (A , _) = ps
                        in (ι (zero , tt))
                         ∷ (σ A λ _ → σ ℕ λ n → ρ (ι (n , tt)) (ι (suc n , tt)))
                         ∷ [] } }

-- META

data Vec {ℓ} (A : Set ℓ) : ℕ → Set ℓ where
  []  : Vec A zero
  _∷_ : A → {n : ℕ} → Vec A n → Vec A (suc n)

Vec-wrapper : DataT VecD
Vec-wrapper (ℓ , _) (A , _) (n , _) = Vec A n

-- META
VecC : DataC VecD Vec-wrapper
VecC = record
  { toN   = λ { (inl refl) → []
              ; (inr (inl (x , n , xs , refl))) → x ∷ xs }
  ; fromN = λ { []       → inl refl
              ; (x ∷ xs) → inr (inl (x , _ , xs , refl)) }
  ; fromN-toN = λ { (inl refl) → refl
                  ; (inr (inl (x , n , xs , refl))) → refl }
  ; toN-fromN = λ { []       → refl
                  ; (x ∷ xs) → refl } }

-- USER

foldVecP : FoldP
foldVecP = fold-operator VecC

-- META

foldVec : {ℓs : (Level × Level × ⊤)} 
         → {A : Set (fst ℓs)} {X : ℕ → Set (fst (snd ℓs))} 
         → X zero → (A → ∀ n → X n → X (suc n)) 
         → ∀ {n} → Vec A n → X n
foldVec e f [] = e
foldVec e f (x ∷ xs) = f x _ (foldVec e f xs)

foldVec-wrapper : FoldT foldVecP
foldVec-wrapper _ ((A , tt) , X , e , f , tt) {(n , tt)} = foldVec e f {n}

foldVec-is-fold : FoldC foldVecP foldVec-wrapper
FoldC.equation foldVec-is-fold (inl refl) = refl
FoldC.equation foldVec-is-fold (inr (inl (x , n , xs , refl))) = refl
