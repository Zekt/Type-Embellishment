{-# OPTIONS --safe --with-K #-}

module Examples.List where

open import Prelude
open import Generics.Telescope
open import Generics.Description
open import Generics.Ornament
open import Generics.Ornament.Description
open import Generics.Ornament.Algebraic
open import Metalib.Datatype
open import Metalib.Connection
open import Utils.Reflection
open import Examples.Nat

ListD = genDataD List
ListC = genDataC ListD List

ListO : DataO ListD NatD
ListO = record
  { level  = λ _ → tt
  ; applyL = λ (ℓ , _) → record
      { param  = λ _ → tt
      ; index  = λ _ _ → tt
      ; applyP = λ (P , _) → ι ∷ ∺ (Δ λ _ → ρ ι ι) ∷ ∺ [] } }

-- length

VecOD : DataOD ListD
VecOD = AlgOD (forget ListC NatC ListO)

VecD' : DataD
VecD' = ⌊ VecOD ⌋ᵈ

VecD : DataD
VecD = record
  { #levels = 1
  ; applyL  = λ { (ℓ , tt) → record
    { alevel = ℓ
    ; Param                 = [ A ∶ Set ℓ ] []
    ; Index                 = λ _ → [] ++ λ _ → [ _ ∶ ℕ ] []
    ; applyP                = λ where
      (A , tt) →
        ι (tt , 0 , tt)
        -- Vec A 0
        ∷ Σ[ _ ∶ A ] Σ[ n ∶ ℕ ] (ρ (ι (tt , n , tt)) (ι (tt , suc n , tt)))
        -- (x : A) → (n : ℕ) → Vec A n → Vec A (suc n)
        ∷ []
    } }
  }

test : VecD' ≡ω VecD
test = refl

-- [FATAL] Agda internal error
-- [TODO] print datatype definitions directly
-- (allow constructor overloading in unquoteDecl data?)
unquoteDecl data Vec constructor vnil vcons = defineByDataD VecD' Vec (vnil ∷ vcons ∷ [])
