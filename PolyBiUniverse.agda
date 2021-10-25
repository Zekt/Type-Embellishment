{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS -v meta:5 #-}
open import Function
open import Function.Base using (case_of_)
open import Data.Nat
open import Data.Nat.Show
open import Data.Bool
open import Data.String using (String) renaming (_++_ to _<>_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; zip)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to join)
open import Data.Empty
open import Data.Unit
open import Data.Maybe using (Maybe; maybe′; just; nothing; fromMaybe)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Category.Monad
open import Reflection
open import Agda.Builtin.Reflection

--------
-- A universe of sums of products

data BiMono : Set₁ where
  ∅   : BiMono -- alternative form of K ⊤
  E   : BiMono -- the element
  I   : BiMono
  K   : Set  → BiMono
  _⊗_ : BiMono → BiMono → BiMono

BiPoly : Set₁
BiPoly = List BiMono

data Mono : Set₁ where
  ∅   : Mono -- alternative form of K ⊤
  I   : Mono
  K   : Set  → Mono
  _⊗_ : Mono → Mono → Mono

Poly : Set₁
Poly = List Mono

elimᴹ : BiMono → Set → Mono
elimᴹ ∅ A = ∅
elimᴹ E A = K A
elimᴹ I A = I
elimᴹ (K X) A = K X
elimᴹ (M ⊗ M') A = elimᴹ M A ⊗ elimᴹ M' A

elim : BiPoly → Set → Poly
elim [] A = []
elim (M ∷ F) A = elimᴹ M A ∷ elim F A


⟦_⟧ᴹ : BiMono → (Set × Set) → Set
⟦ ∅      ⟧ᴹ (X , Y) = ⊤
⟦ E      ⟧ᴹ (X , Y) = X
⟦ I      ⟧ᴹ (X , Y) = Y
⟦ K A    ⟧ᴹ (X , Y) = A
⟦ M ⊗ M' ⟧ᴹ XY = ⟦ M ⟧ᴹ XY × ⟦ M' ⟧ᴹ XY

⟦_⟧ : BiPoly → (Set × Set) → Set
⟦ []    ⟧ XY = ⊥
⟦ M ∷ F ⟧ XY = ⟦ M ⟧ᴹ XY ⊎ ⟦ F ⟧ XY

--fmapᴹ : (M : Mono) {X Y : Set} → (X → Y) → ⟦ M ⟧ᴹ X → ⟦ M ⟧ᴹ Y
--fmapᴹ ∅        f _          = tt
--fmapᴹ I        f x          = f x
--fmapᴹ (K A)    f a          = a
--fmapᴹ (M ⊗ M') f (xs , xs') = fmapᴹ M f xs , fmapᴹ M' f xs'
--
--fmap : (F : Poly) {X Y : Set} → (X → Y) → ⟦ F ⟧ X → ⟦ F ⟧ Y
--fmap (M ∷ F) f (inj₁ xs) = inj₁ (fmapᴹ M f xs)
--fmap (M ∷ F) f (inj₂ xs) = inj₂ (fmap F f xs)

ListF′ : BiPoly
ListF′ = ∅ ∷ E ⊗ I ∷ []

data μ (F : BiPoly) (A : Set) : Set where
  con : ⟦ F ⟧ (A , μ F A) → μ F A

--data γ : (F : BiPoly) → (A : Set) → Set where
--  con : {F : BiPoly} {A : Set} → ⟦ F ⟧ (A , μ F A) → γ F A

module _ (F : BiPoly) {A X : Set} (f : ⟦ F ⟧ (A , X) → X) where
  mutual

    iteration : μ F A → X
    iteration (con ds) = f (mapIter F ds)

    mapIter : (G : BiPoly) (ds : ⟦ G ⟧ (A , μ F A)) → ⟦ G ⟧ (A , X)
    mapIter (M ∷ F) (inj₁ ds) = inj₁ (mapIterᴹ M ds)
    mapIter (M ∷ F) (inj₂ ds) = inj₂ (mapIter F ds)

    mapIterᴹ : (M : BiMono) (ds : ⟦ M ⟧ᴹ (A , μ F A)) → ⟦ M ⟧ᴹ (A , X)
    mapIterᴹ ∅        _          = tt
    mapIterᴹ E        d          = d
    mapIterᴹ I        d          = iteration d
    mapIterᴹ (K A   ) a          = a
    mapIterᴹ (M ⊗ M') (ds , ds') = mapIterᴹ M ds , mapIterᴹ M' ds'

toList   : ∀ {A} → μ ListF′ A → List A
toList (con (inj₁ tt)) = []
toList (con (inj₂ (inj₁ (a , as)))) = a ∷ toList as

fromList : ∀ {A} → List A → μ ListF′ A
fromList []       = con (inj₁ tt)
fromList (x ∷ xs) = con (inj₂ (inj₁ {!!}))

-- mapList : {X Y : Set} → (X → Y) → List X → List Y
---- map : (F : Poly) → {X Y : Set} → (X → Y) → μ F X → μ F Y
--
mapFstᴹ : (M : BiMono) {A B X : Set}
        → (A → B) → ⟦ M ⟧ᴹ (A , X) → ⟦ M ⟧ᴹ (B , X)
mapFstᴹ ∅        f _          = tt
mapFstᴹ E        f x          = f x
mapFstᴹ I        f x          = x
mapFstᴹ (K A)    f a          = a
mapFstᴹ (M ⊗ M') f (xs , xs') = mapFstᴹ M f xs , mapFstᴹ M' f xs'

mapFst : (F : BiPoly) → {A B X : Set}
       → (A → B) → ⟦ F ⟧ (A , X) → ⟦ F ⟧ (B , X)
mapFst (M ∷ F) f (inj₁ FAX) = inj₁ (mapFstᴹ M f FAX)
mapFst (M ∷ F) f (inj₂ FAX) = inj₂ (mapFst F f FAX)

mapF : (F : BiPoly) → {A B : Set} → (A → B) → μ F A → μ F B
mapF F f (con x) = iteration F (con ∘ mapFst F f) (con x)

mapList : {A B : Set} → (A → B) → List A → List B
mapList f = toList ∘ mapF ListF′ f ∘ fromList
