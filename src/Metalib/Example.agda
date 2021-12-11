open import Prelude

module Metalib.Example where

open import Utils.Reflection

open import Generics.Description
open import Metalib.Inductive-ConsTel 

data Rel (A : Set) : (xs ys : List A) → Set where
  
T-rel : Tel _
T-rel = [ A ∶ Set ] [ xs ∶ List A ] [ ys ∶ List A ] []

`T-rel : Telescope
`T-rel = fst $ ⇑ evalT (getDefType (quote Rel))

{-
  ("A" , vArg `Set₀) ∷
  ("xs" , vArg (def (quote List) (hArg (def₀ (quote lzero)) ∷ [ vArg (var₀ 0) ]))) ∷
  "ys" , vArg (def (quote List) (hArg (def₀ (quote lzero)) ∷ [ vArg (var₀ 1) ])) ∷
  []
-}

T-rel' : Tel (lsuc lzero)
T-rel' = evalT (fromTelescope `T-rel) 

_ : T-rel' ≡ T-rel
_ = refl

data Pointwise (A : Set) (B : Set) (R : A → B → Set) : (xs : List A) → (ys : List B) → Set where 

pointwise : Tel _
pointwise = [ A ∶ Set ] [ B ∶ Set ] [ R ∶ (A → B → Set) ] [ xs ∶ List A ] [ ys ∶ List B ] []

Γ-pointwise : Telescope
Γ-pointwise = fst $ ⇑ evalT (getDefType (quote Pointwise))

pointwise' : Tel _
pointwise' = evalT (fromTelescope Γ-pointwise) 

_ : pointwise' ≡ pointwise
_ = refl

not-so-bad : Tel _
not-so-bad = [ b ∶ if true then Bool else ⊥ ] [] 

`not-so-bad : Telescope
`not-so-bad = evalT (toTelescope not-so-bad)

not-so-bad' : Tel _
not-so-bad' = evalT (fromTelescope `not-so-bad)

_ : not-so-bad ≡ not-so-bad'
_ = refl

_ : Set
_ = evalT (unquoteTC (quoteTerm (if true then Bool else ⊥)))

