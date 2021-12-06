{-# OPTIONS --safe #-}
module Prelude.List where

open import Agda.Primitive
open import Agda.Builtin.Nat using (zero; suc; _+_; _*_)
  renaming (Nat to ℕ)

open import Prelude.Function
open import Prelude.Eq
open import Prelude.Show
open import Prelude.Functor
open import Prelude.Relation.PropositionalEquality

open import Prelude.Sigma
open import Prelude.Bool
open import Prelude.Maybe

private variable
  ℓ     : Level
  A B C : Set _

open import Agda.Builtin.List public
  using (List; []; _∷_)

infixr 5 _++_

pattern [_] x = x ∷ []

instance
  ListFunctor : Functor List
  fmap ⦃ ListFunctor ⦄ f []       = []
  fmap ⦃ ListFunctor ⦄ f (x ∷ xs) = f x ∷ fmap f xs

map : {A B : Set} → (A → B) → List A → List B
map = fmap

map-cong : {A B : Set} (f g : A → B) → (∀ x → f x ≡ g x) → (xs : List A) → map f xs ≡ map g xs
map-cong f g eq []       = refl
map-cong f g eq (x ∷ xs) = cong₂ _∷_ (eq x) (map-cong f g eq xs)

map-id : {A : Set} (xs : List A) → map id xs ≡ xs
map-id []       = refl
map-id (x ∷ xs) = cong (x ∷_) (map-id xs)

map-comp : {A B C : Set} (f : B → C) (g : A → B) → (xs : List A) → map (f ∘ g) xs ≡ map f (map g xs)
map-comp f g []       = refl
map-comp f g (x ∷ xs) = cong (f (g x) ∷_) (map-comp f g xs)

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
concatMap f = concat ∘ fmap f

null : List A → Bool
null []       = true
null (x ∷ xs) = false

and : List Bool → Bool
and = foldr _∧_ true

or : List Bool → Bool
or = foldr _∨_ false

any : (A → Bool) → List A → Bool
any p = or ∘ fmap p

all : (A → Bool) → List A → Bool
all p = and ∘ fmap p

sum : List ℕ → ℕ
sum = foldr _+_ 0

product : List ℕ → ℕ
product = foldr _*_ 1

length : List A → ℕ
length = foldr (const suc) 0

elem : ⦃ Eq A ⦄ → A → List A → Bool
elem x = any (x ==_)

span : (A → Bool) → List A → List A × List A
span p []       = [] , []
span p (x ∷ xs) with p x
... | true  = bimap (x ∷_) id (span p xs)
... | false = [] , x ∷ xs

break : (A → Bool) → List A → (List A × List A)
break p = span (not ∘ p)

intersperse : A → List A → List A
intersperse x []       = []
intersperse x [ y ]    = [ y ]
intersperse x (y ∷ ys) = y ∷ x ∷ intersperse x ys

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

instance
  open import Agda.Builtin.String
    using (primStringAppend)
  ShowList : ⦃ Show A ⦄ → Show (List A)
  show ⦃ ShowList ⦄ =
    foldr (λ x xs → primStringAppend (show x) (primStringAppend " ∷ " xs)) "[]"

  EqList : ∀ {a} {A : Set a} ⦃ _ : Eq A ⦄
    → Eq (List A)
  _==_ ⦃ EqList ⦄ []       []       = true
  _==_ ⦃ EqList ⦄ (x ∷ xs) (y ∷ ys) with x == y
  ... | false = false
  ... | true  = xs == ys
  _==_ ⦃ EqList ⦄ _        _ = false
