{-# OPTIONS --without-K --safe #-}
module Prelude.List where

open import Agda.Primitive
open import Agda.Builtin.Nat using (zero; suc; _+_; _*_)
  renaming (Nat to ℕ)

open import Prelude.Nat
open import Prelude.Function
open import Prelude.Eq
open import Prelude.Monoid
open import Prelude.Show
open import Prelude.Functor
open import Prelude.Relation.PropositionalEquality

open import Prelude.Sigma
open import Prelude.Bool
open import Prelude.Maybe

private variable
  ℓ ℓ'  : Level
  A B C : Set _

open import Agda.Builtin.List public
  using (List; []; _∷_)

infixr 5 _++_

pattern [_] x = x ∷ []

map : (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

instance
  FunctorList : Functor List
  fmap ⦃ FunctorList ⦄ = map

map-cong : (f g : A → B) → (∀ x → f x ≡ g x) → (xs : List A) → map f xs ≡ map g xs
map-cong f g eq []       = refl
map-cong f g eq (x ∷ xs) = cong₂ _∷_ (eq x) (map-cong f g eq xs)

map-id : (xs : List A) → map id xs ≡ xs
map-id []       = refl
map-id (x ∷ xs) = cong (x ∷_) (map-id xs)

map-comp : (f : B → C) (g : A → B) → (xs : List A) → map (f ∘ g) xs ≡ map f (map g xs)
map-comp f g []       = refl
map-comp f g (x ∷ xs) = cong (f (g x) ∷_) (map-comp f g xs)

instance
  FunctorLawList : FunctorLaw List
  FunctorLawList = record
    { fmap-cong = map-cong
    ; fmap-id   = map-id
    ; fmap-comp = map-comp
    }

private
  _++_ : List A → List A → List A
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

instance
  SemigroupList : Semigroup (List A)
  _<>_ ⦃ SemigroupList ⦄ = _++_

  MonoidList : Monoid (List A)
  mempty ⦃ MonoidList ⦄ = []

head : List A →  Maybe A
head (x ∷ _) = just x
head [] = nothing

last : List A → Maybe A
last [ x ] = just x
last (_ ∷ xs) = last xs
last [] = nothing

filter : (A → Bool) → List A → List A
filter p []       = []
filter p (x ∷ xs) = if p x
  then x ∷ filter p xs
  else filter p xs

drop : ℕ → List A → List A
drop zero    xs       = xs
drop (suc n) []       = []
drop (suc n) (x ∷ xs) = drop n xs

zipWith : (A → B → C) → List A → List B → List C
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys
zipWith f _        _        = []

zip : List A → List B → List (A × B)
zip = zipWith (_,_)

foldr : B → (A → B → B) → List A → B
foldr z c []       = z
foldr z c (x ∷ xs) = c x (foldr z c xs)

foldl : A → (A → B → A) → List B → A
foldl z c []       = z
foldl z c (x ∷ xs) = foldl (c z x) c xs

concat : List (List A) → List A
concat = foldr [] _++_

concatMap : (A → List B) → List A → List B
concatMap f = concat ∘ fmap f

null : List A → Bool
null []       = true
null (x ∷ xs) = false

and : List Bool → Bool
and = foldr true _∧_

or : List Bool → Bool
or = foldr false _∨_

any : (A → Bool) → List A → Bool
any p = or ∘ fmap p

all : (A → Bool) → List A → Bool
all p = and ∘ fmap p

sum : List ℕ → ℕ
sum = foldr 0 _+_

product : List ℕ → ℕ
product = foldr 1 _*_

length : List A → ℕ
length = foldr 0 (const suc)

removeLast : ∀ {A : Set ℓ} → ℕ → List A → List A
removeLast n [] = []
removeLast n (x ∷ xs) = if (length xs <? n) then
                          []
                        else if (length xs == n) then
                          [ x ]
                        else x ∷ removeLast n xs

elem : ⦃ Eq A ⦄ → A → List A → Bool
elem x = any (x ==_)

span : (A → Bool) → List A → List A × List A
span p []       = [] , []
span p (x ∷ xs) with p x
... | true  = bimap (x ∷_) id (span p xs)
... | false = [] , x ∷ xs

break : (A → Bool) → List A → (List A × List A)
break p = span (not ∘ p)

splitAt : ℕ → List A → List A × List A
splitAt zero            xs       = [] , xs
splitAt (suc _)         []       = [] , []
splitAt (suc zero)      (x ∷ xs) = [ x ] , xs
splitAt (suc m@(suc n)) (x ∷ xs) = let xs' , xs'' = splitAt m xs in
  x ∷ xs' , xs''

intersperse : A → List A → List A
intersperse x []       = []
intersperse x [ y ]    = [ y ]
intersperse x (y ∷ ys) = y ∷ x ∷ intersperse x ys

--------------------------------------------------------------------------
-- Generaion of a list

duplicate : ℕ → A → List A
duplicate zero    x = []
duplicate (suc n) x = x ∷ duplicate n x
------------------------------------------------------------------------
-- Operations for reversing lists

reverseAcc : List A → List A → List A
reverseAcc = λ x → foldl x (flip _∷_)

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

eq : ⦃ _ : Eq A ⦄ → List A → List A → Bool
eq []       []       = true
eq (x ∷ xs) (y ∷ ys) = if x == y then eq xs ys else false
eq _        _        = false

instance
  open import Agda.Builtin.String
    using (primStringAppend)

  EqList : ∀ {a} {A : Set a} ⦃ _ : Eq A ⦄
    → Eq (List A)
  _==_ ⦃ EqList ⦄ = eq

data All {A : Set ℓ} (P : A → Set ℓ') : List A → Set (ℓ ⊔ ℓ') where
  []  : All P []
  _∷_ : {x : A} → P x → {xs : List A} → All P xs → All P (x ∷ xs)

allToList : {A : Set ℓ} {P : A → Set ℓ'} {xs : List A} → All P xs → List (Σ A P)
allToList []        = []
allToList (p ∷ all) = (_ , p) ∷ allToList all

data Any {A : Set ℓ} (P : A → Set ℓ') : List A → Set (ℓ ⊔ ℓ') where
  here  : ∀ {x xs} (px  : P x)      → Any P (x ∷ xs)
  there : ∀ {x xs} (pxs : Any P xs) → Any P (x ∷ xs)

lookupAny : {A : Set ℓ} {P : A → Set ℓ'} {xs : List A} → Any P xs → Σ[ x ∈ A ] P x
lookupAny (here  px ) = _ , px
lookupAny (there pxs) = lookupAny pxs
