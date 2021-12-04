{-# OPTIONS --safe #-}

module Prelude.Nat where

open import Prelude.Relation
open import Prelude.PropositionalEquality

open import Agda.Builtin.Nat public
  using (zero; suc; _+_; _*_; _==_)
  renaming (Nat to ℕ; _<_ to _<ᵇ_; _-_ to _∸_)

suc-inj : {m n : ℕ}
  → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

_≟_ : (m n : ℕ) → Dec (m ≡ n)
zero  ≟ zero  = yes refl
suc m ≟ suc n with m ≟ n
... | yes p = yes (cong suc p)
... | no ¬p = no λ { refl → ¬p refl}
zero  ≟ suc n = no λ ()
suc m ≟ zero  = no λ ()
