open import Prelude

module Generics.Example where

open import Generics.Description


------------------------------------------------------------------------------
-- Data types

NatD : DataD
NatD = record
  { #levels = 0
  ; applyL  = λ { tt → record
    { level  = 0ℓ
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

-- data List (A : Set) : Set where
--   []  : List A
--   _∷_ : A → List A → List A

ListD : DataD
ListD = record
  { #levels = 1
  ; applyL  = λ { (ℓ , _) → record
    { level = ℓ
    ; level-pre-fixed-point = refl
    ; Param = [ A ∶ Set ] []
    ; Index = λ _ → []
    ; applyP = λ where
      (A , tt) →
        ι tt
        -- List A
        ∷ Π[ _ ∶ A ] (ρ (ι tt) (ι tt))
        -- (_ : A) → List A → List A
        ∷ []
    }}
  }

-- data Vec (A : Set) : ℕ → Set where
--   []  : Vec A 0
--   _∷_ : A → Vec A n → Vec A (suc n)
VecD : DataD
VecD = record
  { #levels = 1
  ; applyL  = λ { (ℓ , tt) → record
    { level = ℓ
    ; level-pre-fixed-point = refl
    ; Param                 = [ A ∶ Set ] []
    ; Index                 = λ _ → [ _ ∶ ℕ ] []
    ; applyP                = λ where
      (A , tt) →
        ι (0 , tt)
        -- Vec A 0
        ∷ Π[ _ ∶ A ] Π[ n ∶ ℕ ] (ρ (ι (n , tt)) (ι (suc n , tt)))
        -- (x : A) → (n : ℕ) → Vec A n → Vec A (suc n)
        ∷ []
    } }
  }

-- data _∈_ {ℓ} {A : Set ℓ} : A → List A → Set ℓ where
--   zero : {x : A} {xs : List A} → x ∈ x ∷ xs
--   suc  : {x y : A} {xs : List A}
--        → x ∈ xs → x ∈ y ∷ xs

∈D : DataD
∈D = record
  { #levels = 1
  ; applyL  = λ where
    (ℓ , _) → record
      { level = ℓ
      ; level-pre-fixed-point = refl
      ; Param = [ A ∶ Set ℓ ] []
      ; Index = λ {(A , _) → [ _ ∶ A ] [ _ ∶ List A ] []}
      ; applyP = λ { (A , _) →
        Π[ x ∶ A ] Π[ xs ∶ List A ] (ι (x , x ∷ xs , tt))
        -- (x : A) → (xs : List A) → x ∈ x ∷ xs
        ∷ Π[ x ∶ A ] Π[ y ∶ A ] Π[ xs ∶ List A ] (ρ (ι (x , xs , tt)) (ι (x , y ∷ xs , tt)))
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
      { level = ℓ ⊔ ℓ'
      ; level-pre-fixed-point = refl
      ; Param = [ A ∶ Set ℓ ] [ B ∶ (A → Set ℓ') ] []
      ; Index = λ _ → []
      ; applyP = λ where
        (A , B , _) →
          Π[ x ∶ A ] ρ (Π[ _ ∶ B x ] ι _) (ι _)
          -- (x : A) → ((_ : B x) → W A B) → W A B
          ∷ []
      }
  }
