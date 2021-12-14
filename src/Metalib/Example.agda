{-# OPTIONS -v meta:10  #-}
open import Prelude
  hiding ([_,_])

module Metalib.Example where

open import Utils.Reflection

open import Generics.Description
open import Generics.Telescope
open import Generics.Example

open import Metalib.Telescope

------------------------------------------------------------------------------
-- 
`T-Nat : Telescope × Type
`T-Nat = getTelescopeT ℕ

_ : evalT (fromTelescope $ fst `T-Nat) ≡ []
_ = refl

_ : evalT(toTelescope $ []) ≡ fst `T-Nat
_ = refl

------------------------------------------------------------------------------
-- Level-polymorphic telescope

`T-List : Telescope × Type
`T-List = getTelescopeT List

T-List : Tel 0ℓ
T-List = {! !}

------------------------------------------------------------------------------
-- 

data Rel (A : Set) : (xs ys : List A) → Set where
  
`T-rel : Telescope × Type
`T-rel = getTelescopeT Rel

_ : evalT (fromTelescope $ fst `T-rel) ≡ [ B ∶ Set ] [ bs ∶ List B ] [ bs ∶ List B ] []
_ = refl

_ : evalT (toTelescope $ [ A ∶ Set ] [ xs ∶ List A ] [ ys ∶ List A ] []) ≡ fst `T-rel -- fst `T-rel
_ = refl


------------------------------------------------------------------------------
-- 

data Pointwise (A : Set) (B : Set) (R : A → B → Set) : (xs : List A) → (ys : List B) → Set where 

T-pointwise : Telescope
T-pointwise = fst $ getTelescopeT Pointwise 

_ : evalT (fromTelescope T-pointwise)
  ≡ [ A ∶ Set ] [ B ∶ Set ] [ R ∶ (A → B → Set) ] [ as ∶ List A ] [ bs ∶ List B ] []
_ = refl

_ : evalT (toTelescope $ [ A ∶ Set ] [ B ∶ Set ] [ R ∶ (A → B → Set) ] [ xs ∶ List A ] [ ys ∶ List B ] []) ≡ T-pointwise
_ = refl

-- Okay but unusual examples
sort-is-not-normal : Tel _
sort-is-not-normal = [ b ∶ if true then Bool else ⊥ ] [] 

`sort-is-not-normal : Telescope
`sort-is-not-normal = evalT (toTelescope sort-is-not-normal)

_ : sort-is-not-normal ≡ [ b ∶ Bool ] []
_ = refl

_ : `sort-is-not-normal ≢ evalT (toTelescope ([ b ∶ Bool ] []))
_ = λ { () }

ex₁ : Bool → Tel _
ex₁ = λ b → []

`ex₁ : Telescope
`ex₁ =  evalT (toTelescope $ Bool ∷ ex₁) 

-- Not really a telescope: 
bad : Tel _
bad = [ b ∶ Bool ] (case b of λ { true → [ n ∶ ℕ ] [] ; false → [] })

_ : Telescope
_ = {!evalT (toTelescope bad)!} -- when ?
