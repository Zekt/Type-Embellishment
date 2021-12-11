open import Prelude

module Metalib.Example where

open import Utils.Reflection

open import Generics.Description
open import Metalib.Inductive-ConsTel 

data Rel (A : Set) : (xs ys : List A) → Set where
  
`T-rel : Telescope
`T-rel = fst $ ⇑ evalT (getDefType (quote Rel))

_ : evalT (fromTelescope `T-rel) ≡ [ B ∶ Set ] [ bs ∶ List B ] [ bs ∶ List B ] []
_ = refl

_ : evalT (toTelescope $ [ A ∶ Set ] [ xs ∶ List A ] [ ys ∶ List A ] []) ≡ `T-rel
_ = refl

data Pointwise (A : Set) (B : Set) (R : A → B → Set) : (xs : List A) → (ys : List B) → Set where 

T-pointwise : Telescope
T-pointwise = fst $ ⇑ evalT (getDefType (quote Pointwise))

_ : evalT (fromTelescope T-pointwise)
  ≡ [ A ∶ Set ] [ B ∶ Set ] [ R ∶ (A → B → Set) ] [ as ∶ List A ] [ bs ∶ List B ] []
_ = refl

_ : evalT (toTelescope $ [ A ∶ Set ] [ B ∶ Set ] [ R ∶ (A → B → Set) ] [ xs ∶ List A ] [ ys ∶ List B ] []) ≡ T-pointwise
_ = refl

not-so-bad : Tel _
not-so-bad = [ b ∶ if true then Bool else ⊥ ] [] 

`not-so-bad : Telescope
`not-so-bad = evalT (toTelescope not-so-bad)

_ : not-so-bad ≡ [ b ∶ Bool ] []
_ = refl

_ : `not-so-bad ≢ evalT (toTelescope ([ b ∶ Bool ] []))
_ = λ { () }

_ : Set
_ = evalT (unquoteTC (quoteTerm (if true then Bool else ⊥)))

