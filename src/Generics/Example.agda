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
      _ → ι tt ∷ ρ (ι tt) (ι tt) ∷ []
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
      (A , tt) → ι tt ∷ σ A (λ _ → ρ (ι tt) (ι tt)) ∷ []
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
        ∷ σ A (λ _ → σ ℕ λ n → ρ (ι (n , tt)) (ι (suc n , tt)))
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
      ; level-pre-fixed-point = {!!}
      ; Param = [ A ∶ Set ℓ ] []
      ; Index = λ {(A , _) → [ _ ∶ A ] [ _ ∶ List A ] []}
      ; applyP = λ { (A , _) →
        σ {!A!} (λ x → σ {!List A!} λ xs → ι ({!!} , {!!} , tt))
        ∷ σ {!!} (λ x → σ {!!} λ y → σ {!!} (λ xs → ρ (ι ({!!} , {!!} , tt)) (ι ({!!} , {!!} ∷ {!!} , tt))))
        ∷ []}
      }
  }
