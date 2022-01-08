{-# OPTIONS --safe #-}
module Tests.SCMTest where

open import Prelude
open import Generics.Safe.Telescope; open ∀ℓ; open ∀ᵗ
open import Generics.Safe.Description
open import Generics.Safe.Description.FixedPoint
open import Generics.Safe.Algebra
open import Generics.Safe.Recursion
open import Generics.Safe.RecursionScheme
open import Generics.Safe.Ornament
open import Generics.Safe.Ornament.Description
open import Generics.Safe.Ornament.Algebraic
open import Generics.Safe.Ornament.Algebraic.Isomorphism
open import Generics.Safe.Ornament.Promotion



---- List 

-- META
ListD : DataD
ListD = record
  { #levels = 1
  ; applyL  = λ ℓs → let (ℓ , _) = ℓs in record
      { alevel = ℓ
      ; level-pre-fixed-point = refl
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
foldList-alg : ∀ {ℓ} → ∀ℓ 1 (λ ℓs → ∀ᵗ false (Set (fst ℓs) ∷ (λ _ → [])) 
           (λ ps →
            {X : ∀ᵗ true [] (λ _ → Set ℓ)} →
            ∀ᵗ true ((X $$ tt) ∷
                      (λ _ → (fst ps → X $$ tt → X $$ tt) ∷ (λ _ → []))) 
            (λ _ →
              Algebra ((ι tt) ∷ (σ (fst ps) (λ _ → ρ (ι tt) (ι tt)) ∷ [])) ℓ)))
foldList-alg = fold-alg ListD

-- META

foldList : {ℓ ℓ₁ : Level} {A : Set ℓ₁} {X : Set ℓ} → X → (A → X → X) → List A → X
foldList e f [] = e
foldList e f (x ∷ xs) = f x (foldList e f xs)

foldList-wrapper : ∀ {ℓ} → ∀ℓ 1 λ ℓs → ∀ᵗ false (Set (fst ℓs) ∷ (λ _ → [])) 
               (λ ps →
                {X : ∀ᵗ false [] (λ _ → Set ℓ)} →
                ∀ᵗ true ((X $$ tt) ∷ 
                          λ _ → (fst ps → X $$ tt → X $$ tt) ∷ λ _ → []) 
                (λ args →
                 FoldT ListC (foldList-alg $$ ℓs $$ ps $$ args)))
foldList-wrapper $$ _ $$ (A , _) $$ (e , f , _) = foldList e f
 
-- META

foldList-is-fold : ∀ {ℓ ℓs ps} {X : Set ℓ} 
                 → (e : X) (f : fst ps →  X → X)
                 → AlgebraC ListC (foldList-alg     $$ ℓs $$ ps $$ (e , f , _))
                                  (foldList-wrapper $$ ℓs $$ ps $$ (e , f , _))
foldList-is-fold e f (inl refl)                  = refl
foldList-is-fold e f (inr (inl (x , xs , refl))) = refl

---- Internally & Enternally Labelled Binary Tree

data IETree {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  tip : A → IETree A B
  bin : B → IETree A B → IETree A B → IETree A B
  
IETreeD : DataD
IETreeD = record
  { #levels = 2
  ; applyL  = λ ℓs → let (ℓ , ℓ' , _) = ℓs in record
      { alevel = ℓ ⊔ ℓ'
      ; level-pre-fixed-point = refl
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

-- USER (specialising a generic library component)
IETree-alg : ∀ {ℓ} → ∀ℓ 2 (λ ℓs → ∀ᵗ false (Set (fst ℓs) ∷ (λ _ → Set (fst (snd ℓs)) ∷ (λ _ → []))) 
           (λ ps →
            {X : ∀ᵗ false [] (λ _ → Set ℓ)} →
            let (A , B , _) = ps
            in ∀ᵗ true ( (A → (X $$ tt)) 
                        ∷ λ _ → (B → X $$ tt → X $$ tt → X $$ tt) 
                        ∷ λ _ → []) 
            (λ _ → Algebra ( (σ A λ _ → ι tt)
                           ∷ (σ B λ _ → ρ (ι tt) (ρ (ι tt) (ι tt)))
                           ∷ []) ℓ)))
IETree-alg $$ ℓs $$ ps $$ fs = fold-alg IETreeD $$ ℓs $$ ps $$ fs
-- IETree-alg = fold-alg IETreeD

-- META

foldIE : {ℓ ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {X : Set ℓ} 
       → (A → X) → (B → X → X → X) → IETree A B → X
foldIE g f (tip x) = g x
foldIE g f (bin y t u) = f y (foldIE g f t) (foldIE g f u)

foldIE-wrapper : ∀ {ℓ} → ∀ℓ 2 λ ℓs → ∀ᵗ false (Set (fst ℓs) ∷ (λ _ → Set (fst (snd ℓs)) ∷ (λ _ → []))) 
               (λ ps →
                {X : ∀ᵗ false [] (λ _ → Set ℓ)} →
                let (A , B , _) = ps
                in ∀ᵗ true ((A → X $$ tt) ∷ 
                          λ _ → (B → X $$ tt → X $$ tt → X $$ tt) ∷ λ _ → []) 
                (λ args →
                 FoldT IETreeC (IETree-alg $$ ℓs $$ ps $$ args)))
foldIE-wrapper $$ _ $$ (A , B , _) $$ (g , f , _) = foldIE g f

-- META

foldIE-is-fold : ∀ {ℓ ℓs ps} {X : Set ℓ} 
                 → (g : fst ps → X) (f : fst (snd ps) → X → X → X)
                      → AlgebraC IETreeC (IETree-alg     $$ ℓs $$ ps $$ (g , f , _))
                                         (foldIE-wrapper $$ ℓs $$ ps $$ (g , f , _))
foldIE-is-fold g f (inl (x , refl)) = refl
foldIE-is-fold g f (inr (inl (y , t , u , refl))) = refl


---- Hand-Crafted Vectors

-- META
VecD : DataD
VecD = record
  { #levels = 1
  ; applyL  = λ ℓs → let (ℓ , _) = ℓs in record
      { alevel = ℓ
      ; level-pre-fixed-point = refl
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


Vec-alg : ∀ {ℓ} → ∀ℓ 1 (λ ℓs → ∀ᵗ false (Set (fst ℓs) ∷ (λ _ → [])) 
           (λ ps →
            {X : ∀ᵗ true (ℕ ∷ (λ _ → [])) (λ _ → Set ℓ)} →
            ∀ᵗ true ((X $$ (zero , tt))
                     ∷ (λ _ → (fst ps → (n : ℕ) → X $$ (n , tt) → X $$ (suc n , tt))
                     ∷ (λ _ → []))) 
            (λ _ → Algebra ((ι (zero , tt))
                           ∷ (σ (fst ps) λ _ → σ ℕ λ n → ρ (ι (n , tt)) (ι (suc n , tt)))
                           ∷ []) ℓ)))
Vec-alg = fold-alg VecD