{-# OPTIONS -v meta:5 #-}
open import Function
open import Function.Base using (case_of_)
open import Data.Nat
open import Data.Nat.Show
open import Data.Bool
open import Data.String using (String) renaming (_++_ to _<>_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; zip)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty
open import Data.Unit
open import Data.Maybe using (Maybe; maybe′; just; nothing; fromMaybe)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Category.Monad
open import Relation.Binary.PropositionalEquality
open import Reflection
--open import Reflection.Traversal ? ?
open import Agda.Builtin.Reflection

--------
-- A universe of sums of products

data Mono : Set₁ where
  ∅   : Mono -- alternative form of K ⊤
  I   : Mono
  K   : Set  → Mono
  _⊗_ : Mono → Mono → Mono

Poly : Set₁
Poly = List Mono

⟦_⟧ᴹ : Mono → Set → Set
⟦ ∅      ⟧ᴹ X = ⊤
⟦ I      ⟧ᴹ X = X
⟦ K A    ⟧ᴹ X = A
⟦ M ⊗ M' ⟧ᴹ X = ⟦ M ⟧ᴹ X × ⟦ M' ⟧ᴹ X

⟦_⟧ : Poly → Set → Set
⟦ []    ⟧ X = ⊥
⟦ M ∷ F ⟧ X = ⟦ M ⟧ᴹ X ⊎ ⟦ F ⟧ X

fmapᴹ : (M : Mono) {X Y : Set} → (X → Y) → ⟦ M ⟧ᴹ X → ⟦ M ⟧ᴹ Y
fmapᴹ ∅        f _          = tt
fmapᴹ I        f x          = f x
fmapᴹ (K A)    f a          = a
fmapᴹ (M ⊗ M') f (xs , xs') = fmapᴹ M f xs , fmapᴹ M' f xs'

fmap : (F : Poly) {X Y : Set} → (X → Y) → ⟦ F ⟧ X → ⟦ F ⟧ Y
fmap (M ∷ F) f (inj₁ xs) = inj₁ (fmapᴹ M f xs)
fmap (M ∷ F) f (inj₂ xs) = inj₂ (fmap F f xs)

data μ (F : Poly) : Set where
  con : ⟦ F ⟧ (μ F) → μ F


-- Specialising to lists
ListF : Set → Poly
ListF A = ∅ ∷ (K A ⊗ I) ∷ []

--data Dep : ℕ → Set where
--  nilV  : Dep zero
--  consV : {n : ℕ} → (m : ℕ) → Dep n → Dep (n + m)

toList : {A : Set} → μ (ListF A) → List A
toList (con (inj₁ tt))              = []
toList (con (inj₂ (inj₁ (a , as)))) = a ∷ toList as

fromList : {A : Set} → List A → μ (ListF A)
fromList []       = con (inj₁ tt)
fromList (a ∷ as) = con (inj₂ (inj₁ (a , fromList as)))

conList : {A : Set} → ⟦ ListF A ⟧ (List A) → List A
conList {A} = toList ∘ con ∘ fmap (ListF A) fromList
  -- transporting con by univalence?

conList' : {A : Set} → ⊤ ⊎ A × List A ⊎ ⊥ → List A
conList' (inj₁ tt)              = conList (inj₁ tt)
conList' (inj₂ (inj₁ (a , as))) = conList (inj₂ (inj₁ (a , as)))
  -- make toList ∘ fromList = id definitionally (in effect)?
  --   check Allais et al's 'New equations for neutral terms' (DTP 2013)
  -- making toList and fromList meet may be problematic (e.g., when involving if_then_else_)

--------
-- Iteration (fold)

module _ (F : Poly) {X : Set} (f : ⟦ F ⟧ X → X) where

  mutual

    iteration : μ F → X
    iteration (con ds) = f (mapIter F ds)

    mapIter : (G : Poly) (ds : ⟦ G ⟧ (μ F)) → ⟦ G ⟧ X
    mapIter (M ∷ F) (inj₁ ds) = inj₁ (mapIterᴹ M ds)
    mapIter (M ∷ F) (inj₂ ds) = inj₂ (mapIter F ds)

    mapIterᴹ : (M : Mono) (ds : ⟦ M ⟧ᴹ (μ F)) → ⟦ M ⟧ᴹ X
    mapIterᴹ ∅        _          = tt
    mapIterᴹ I        d          = iteration d
    mapIterᴹ (K A   ) a          = a
    mapIterᴹ (M ⊗ M') (ds , ds') = mapIterᴹ M ds , mapIterᴹ M' ds'

-- Specialising to lists

iterList : {A X : Set} → (⟦ ListF A ⟧ X → X) → List A → X
iterList {A} alg as = iteration (ListF A) alg (fromList as)

iterList' : {A X : Set} → (⟦ ListF A ⟧ X → X) → List A → X
iterList' {A} alg []       = iteration (ListF A) alg (fromList [])
iterList' {A} alg (a ∷ as) = iteration (ListF A) alg (fromList (a ∷ as))
  -- have to deal with recursion

-- Curried fold
Algᴹ : (M : Mono) → Set → Set → Set
Algᴹ ∅        X Y = Y
Algᴹ I        X Y = X → Y
Algᴹ (K A   ) X Y = A → Y
Algᴹ (M ⊗ M') X Y = Algᴹ M X (Algᴹ M' X Y)

Alg : (F : Poly) → Set → Set → Set
Alg []      X Y = Y
Alg (M ∷ F) X Y = Algᴹ M X X → Alg F X Y
  -- Y is supposed to be 'the end' of Alg

fromAlgᴹ : (M : Mono) {X Y : Set} → Algᴹ M X Y → ⟦ M ⟧ᴹ X → Y
fromAlgᴹ ∅        alg _ = alg
fromAlgᴹ I        alg = alg
fromAlgᴹ (K A   ) alg = alg
fromAlgᴹ (M ⊗ M') alg (xs , xs') = fromAlgᴹ M' (fromAlgᴹ M alg xs) xs'

toAlg : (F : Poly) {X Y : Set} → ((⟦ F ⟧ X → X) → Y) → Alg F X Y
toAlg []      f = f λ ()
toAlg (M ∷ F) f alg = toAlg F λ g → f λ { (inj₁ xs) → fromAlgᴹ M alg xs
                                        ; (inj₂ xs) → g xs }

fold : (F : Poly) → {X : Set} → Alg F X (μ F → X)
fold F = toAlg F (iteration F)

--------

foldr : {A X : Set} → Alg (ListF A) X (List A → X)
foldr {A} e f as = fold (ListF A) e f (fromList as)

foldr' : {A X : Set} → X → (A → X → X) → List A → X
foldr' {A} e f []       =  fold (ListF A) e f (fromList []) 
foldr' {A} e f (a ∷ as) =  fold (ListF A) e f (fromList (a ∷ as)) 
  -- in general derived definitions

