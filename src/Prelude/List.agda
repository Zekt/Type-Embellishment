{-# OPTIONS --safe #-}
module Prelude.List where

open import Agda.Primitive
open import Agda.Builtin.Nat using (zero; suc; _+_; _*_)
  renaming (Nat to ℕ)

open import Prelude.Function
open import Prelude.Sigma
open import Prelude.Bool
open import Prelude.Fin
open import Prelude.Maybe
  hiding (map)
open import Prelude.Relation

private variable
  ℓ     : Level
  A B C : Set _
  
open import Agda.Builtin.List public
  using (List; []; _∷_)

infixr 5 _++_

pattern [_] x = x ∷ []

map : (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

_++_ : List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

zipWith : (A → B → C) → List A → List B → List C
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys
zipWith f _        _        = []

zip : List A → List B → List (A × B)
zip = zipWith (_,_)

foldr : (A → B → B) → B → List A → B
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

foldl : (A → B → A) → A → List B → A
foldl c n []       = n
foldl c n (x ∷ xs) = foldl c (c n x) xs

concat : List (List A) → List A
concat = foldr _++_ []

concatMap : (A → List B) → List A → List B
concatMap f = concat ∘ map f

null : List A → Bool
null []       = true
null (x ∷ xs) = false

and : List Bool → Bool
and = foldr _∧_ true

or : List Bool → Bool
or = foldr _∨_ false

any : (A → Bool) → List A → Bool
any p = or ∘ map p

all : (A → Bool) → List A → Bool
all p = and ∘ map p

sum : List ℕ → ℕ
sum = foldr _+_ 0

product : List ℕ → ℕ
product = foldr _*_ 1

length : List A → ℕ
length = foldr (const suc) 0

span : {P : A → Set ℓ} → ((x : A) → Dec (P x)) → List A → (List A × List A)
span P? []       = ([] , [])
span P? (x ∷ xs) with does (P? x)
... | true  = bimap (x ∷_) id (span P? xs)
... | false = ([] , x ∷ xs)

break : {P : A → Set ℓ} → ((x : A) → Dec (P x)) → List A → (List A × List A)
break P? = span λ x → ¬? (P? x)

------------------------------------------------------------------------
-- Operations for reversing lists

reverseAcc : List A → List A → List A
reverseAcc = foldl (flip _∷_)

reverse : List A → List A
reverse = reverseAcc []

lookup : (xs : List A) → ℕ → Maybe A
lookup (x ∷ xs) zero    = just x
lookup (x ∷ xs) (suc i) = lookup xs i
lookup []       _       = nothing

data SnocView {A : Set ℓ} : List A → Set ℓ where
  []    : SnocView []
  _∷ʳ_ : (xs : List A) (x : A) → SnocView (xs ++ [ x ])

snocView : (xs : List A) → SnocView xs
snocView []               = []
snocView (x ∷ xs)         with snocView xs
... | []      = [] ∷ʳ x
... | ys ∷ʳ y = (x ∷ ys) ∷ʳ y
