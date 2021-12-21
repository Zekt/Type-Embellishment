{-# OPTIONS --without-K #-}

open import Prelude

module Generics.Example where

open import Generics.Telescope
open import Generics.Description
open import Generics.Algebra
open import Generics.Recursion

------------------------------------------------------------------------------
-- Data types

NatD : DataD
NatD = record
  { #levels = 0
  ; applyL  = λ { tt → record
    { alevel  = 0ℓ
    ; level-pre-fixed-point = refl
    ; Param  = []
    ; Index  = λ _ → []
    ; applyP = λ where
      _ → ι tt 
        -- ℕ
        ∷ ρ (ι tt) (ι tt) ∷ []
        -- ℕ → ℕ
    }}
  }

-- data List (A : Set ℓ) : Set ℓ where
--   []  : List A
--   _∷_ : A → List A → List A

ListD : DataD
ListD = record
  { #levels = 1
  ; applyL  = λ { (ℓ , _) → record
    { alevel = ℓ
    ; level-pre-fixed-point = refl
    ; Param = [ A ∶ Set ℓ ] []
    ; Index = λ _ → []
    ; applyP = λ where
      (A , tt) →
        ι tt
        -- List A
        ∷ Σ[ _ ∶ A ] (ρ (ι tt) (ι tt))
        -- (_ : A) → List A → List A
        ∷ []
    }}
  }

data Vec (A : Set ℓ) : ℕ → Set ℓ where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

VecD : DataD
VecD = record
  { #levels = 1
  ; applyL  = λ { (ℓ , tt) → record
    { alevel = ℓ
    ; level-pre-fixed-point = refl
    ; Param                 = [ A ∶ Set ℓ ] []
    ; Index                 = λ _ → [ _ ∶ ℕ ] []
    ; applyP                = λ where
      (A , tt) →
        ι (0 , tt)
        -- Vec A 0
        ∷ Σ[ _ ∶ A ] Σ[ n ∶ ℕ ] (ρ (ι (n , tt)) (ι (suc n , tt)))
        -- (x : A) → (n : ℕ) → Vec A n → Vec A (suc n)
        ∷ []
    } }
  }

data _∈_ {ℓ} {A : Set ℓ} : A → List A → Set ℓ where
  zero : {x : A} {xs : List A} → x ∈ (x ∷ xs)
  suc  : {x y : A} {xs : List A}
       → x ∈ xs → x ∈ (y ∷ xs)

∈D : DataD
∈D = record
  { #levels = 1
  ; applyL  = λ where
    (ℓ , _) → record
      { alevel = ℓ
      ; level-pre-fixed-point = refl
      ; Param = [ A ∶ Set ℓ ] []
      ; Index = λ {(A , _) → [ _ ∶ A ] [ _ ∶ List A ] []}
      ; applyP = λ { (A , _) →
        Σ[ x ∶ A ] Σ[ xs ∶ List A ] (ι (x , x ∷ xs , tt))
        -- (x : A) → (xs : List A) → x ∈ x ∷ xs
        ∷ Σ[ x ∶ A ] Σ[ y ∶ A ] Σ[ xs ∶ List A ] (ρ (ι (x , xs , tt)) (ι (x , y ∷ xs , tt)))
        -- (x : A) → (y : A) → (xs : List A) → x ∈ xs → x ∈ y ∷ xs
        ∷ []}
      }
  }

data W (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  sup : (x : A) → ((t : B x) → W A B) → W A B

WD : DataD
WD = record
  { #levels = 2
  ; applyL  = λ where
    (ℓ , ℓ' , tt) → record
      { alevel = ℓ ⊔ ℓ'
      ; level-pre-fixed-point = refl
      ; Param = [ A ∶ Set ℓ ] [ B ∶ (A → Set ℓ') ] []
      ; Index = λ _ → []
      ; applyP = λ where
        (A , B , _) →
          Σ[ x ∶ A ] ρ (Π[ t ∶ B x ] ι _) (ι _)
          -- (x : A) → ((_ : B x) → W A B) → W A B
          ∷ []
      }
  }
