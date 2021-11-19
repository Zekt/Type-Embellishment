{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS -v meta:5 #-}
open import Function
open import Function.Base using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.Nat
open import Data.Nat.Show
open import Data.Bool
open import Data.String using (String) renaming (_++_ to _<>_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; zip)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to join)
open import Data.Empty
open import Data.Unit
open import Data.Maybe using (Maybe; maybe′; just; nothing; fromMaybe)
open import Data.List using (List; []; _∷_; _++_)
open import Category.Monad
open import Reflection
open import Agda.Builtin.Reflection

--------
-- A universe of sums of products

data BiMono : Set₁ where
  ∅   : BiMono -- alternative form of K ⊤
  E   : BiMono -- the element
  I   : BiMono
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
elimᴹ (M ⊗ M') A = elimᴹ M A ⊗ elimᴹ M' A

elim : BiPoly → Set → Poly
elim [] A = []
elim (M ∷ F) A = elimᴹ M A ∷ elim F A


⟦_⟧ᴹ : BiMono → (Set × Set) → Set
⟦ ∅      ⟧ᴹ (X , Y) = ⊤
⟦ E      ⟧ᴹ (X , Y) = X
⟦ I      ⟧ᴹ (X , Y) = Y
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
fmapᴹ : (M : BiMono) {A B X Y : Set}
      → (A → B) → (X → Y) → ⟦ M ⟧ᴹ (A , X) → ⟦ M ⟧ᴹ (B , Y)
fmapᴹ ∅        f g _          = tt
fmapᴹ E        f g x          = f x
fmapᴹ I        f g x          = g x
fmapᴹ (M ⊗ M') f g (xs , xs') = fmapᴹ M f g xs , fmapᴹ M' f g xs'

fmap : (F : BiPoly) → {A B X Y : Set}
     → (A → B) → (X → Y) → ⟦ F ⟧ (A , X) → ⟦ F ⟧ (B , Y)
fmap (M ∷ F) f g (inj₁ FAX) = inj₁ (fmapᴹ M f g FAX)
fmap (M ∷ F) f g (inj₂ FAX) = inj₂ (fmap F f g FAX)

mapFstᴹ : (M : BiMono) {A B X : Set}
        → (A → B) → ⟦ M ⟧ᴹ (A , X) → ⟦ M ⟧ᴹ (B , X)
mapFstᴹ ∅        f _          = tt
mapFstᴹ E        f x          = f x
mapFstᴹ I        f x          = x
mapFstᴹ (M ⊗ M') f (xs , xs') = mapFstᴹ M f xs , mapFstᴹ M' f xs'

mapFst : (F : BiPoly) → {A B X : Set}
       → (A → B) → ⟦ F ⟧ (A , X) → ⟦ F ⟧ (B , X)
mapFst (M ∷ F) f (inj₁ FAX) = inj₁ (mapFstᴹ M f FAX)
mapFst (M ∷ F) f (inj₂ FAX) = inj₂ (mapFst F f FAX)

mapSndᴹ : (M : BiMono) {A X Y : Set}
        → (X → Y) → ⟦ M ⟧ᴹ (A , X) → ⟦ M ⟧ᴹ (A , Y)
mapSndᴹ ∅        f _          = tt
mapSndᴹ E        f x          = x
mapSndᴹ I        f x          = f x
mapSndᴹ (M ⊗ M') f (xs , xs') = mapSndᴹ M f xs , mapSndᴹ M' f xs'

mapSnd : (F : BiPoly) → {A X Y : Set}
       → (X → Y) → ⟦ F ⟧ (A , X) → ⟦ F ⟧ (A , Y)
mapSnd (M ∷ F) f (inj₁ FAX) = inj₁ (mapSndᴹ M f FAX)
mapSnd (M ∷ F) f (inj₂ FAX) = inj₂ (mapSnd F f FAX)

mapF : (F : BiPoly) → {A B : Set} → (A → B) → μ F A → μ F B
mapF (∅ ∷ F) f (con (inj₁ tt)) = con (inj₁ tt)
mapF (E ∷ F) f (con (inj₁ x)) = con (inj₁ (f x))
mapF (I ∷ F) f (con (inj₁ x)) = con (inj₁ {!!})
mapF ((M ⊗ M₁) ∷ F) f (con (inj₁ (m₁ , m₂))) =
  con (inj₁ (fmapᴹ M f {!!} m₁ , fmapᴹ M₁ f {!!} m₂))
mapF (_ ∷ F) f (con (inj₂ y)) = con (inj₂ (fmap F f {!!} y))

--iteration F (con ∘ mapFst F f) (con x)

length′ : {A : Set} → μ ListF′ A → ℕ
length′ (con (inj₁ tt))              = 0
length′ (con (inj₂ (inj₁ (x , xs)))) = suc (length′ xs)

length : {A : Set} → List A → ℕ
length []       = 0
length (x ∷ xs) = suc (length xs)

append′ : {A : Set} → μ ListF′ A → μ ListF′ A → μ ListF′ A
append′ (con (inj₁ tt)) ys              = ys
append′ (con (inj₂ (inj₁ (x , xs)))) ys = con (inj₂ (inj₁ (x , (append′ xs ys))))

append : {A : Set} → List A → List A → List A
append [] ys = []
append (x ∷ xs) ys = x ∷ append xs ys

mapList : {A B : Set} → (A → B) → List A → List B
mapList f = toList ∘ mapF ListF′ f ∘ fromList

data Color : Set where
  Red : Color
  Black : Color

data RBTree (A : Set) : Color → Set where
  leaf  : RBTree A Black
  nodeR : A → RBTree A Black → RBTree A Black → RBTree A Red
  nodeB : {c1 c2 : Color}
        → A → RBTree A c1    → RBTree A c2    → RBTree A Black
mapRBTree : ∀ {A B c} → (A → B) → RBTree A c → RBTree B c
mapRBTree f leaf           = leaf
mapRBTree f (nodeR x t₁ t₂) = nodeR (f x) (mapRBTree f t₁) (mapRBTree f t₂)
mapRBTree f (nodeB x t₁ t₂) = nodeB (f x) (mapRBTree f t₁) (mapRBTree f t₂)

{-  For slides

map : (F : BiPoly) → {A B : Set} → (A → B) → μ F A → μ F B
map F {A} {B} f (con xs) = con (mapᴾ F xs)
  where
    mapᴹ : (M : BiMono) → ⟦ M ⟧ᴹ (A , μ F A) → ⟦ M ⟧ᴹ (B , μ F B)
    mapᴹ ∅       tt        = tt
    mapᴹ E       a         = f a        -- apply f to an element
    mapᴹ I       x         = map F f x  -- recursive call
    mapᴹ (K C)   c         = c
    mapᴹ (M ⊗ N) (xs , ys) = mapᴹ M xs , mapᴹ N ys

    mapᴾ : (G : BiPoly) → ⟦ G ⟧ (A , μ F A) → ⟦ G ⟧ (B , μ F B)
    mapᴾ (M ∷ G) (inj₁ xs) = inj₁ (mapᴹ M  xs)  -- preserving
    mapᴾ (M ∷ G) (inj₂ xs) = inj₂ (mapᴾ Ms xs)  -- constructor choice

-}

-- For subsequent proofs

module Map (F : BiPoly) {A B : Set} (f : A → B) where

  mutual

    mapᴹ : (M : BiMono) → ⟦ M ⟧ᴹ (A , μ F A) → ⟦ M ⟧ᴹ (B , μ F B)
    mapᴹ ∅       tt        = tt
    mapᴹ E       a         = f a
    mapᴹ I       x         = map x
    mapᴹ (M ⊗ N) (xs , ys) = mapᴹ M xs , mapᴹ N ys

    mapᴾ : (G : BiPoly) → ⟦ G ⟧ (A , μ F A) → ⟦ G ⟧ (B , μ F B)
    mapᴾ (M ∷ G) (inj₁ xs) = inj₁ (mapᴹ M xs)
    mapᴾ (M ∷ G) (inj₂ xs) = inj₂ (mapᴾ G xs)

    map : μ F A → μ F B
    map (con xs) = con (mapᴾ F xs)

module _ (F : BiPoly) {A : Set} where

  open Map F {A} id

  mutual

    mapᴹ-id : (M : BiMono) (xs : ⟦ M ⟧ᴹ (A , μ F A)) → mapᴹ M xs ≡ xs
    mapᴹ-id ∅       tt        = refl
    mapᴹ-id E       a         = refl
    mapᴹ-id I       x         = map-id x
    mapᴹ-id (M ⊗ N) (xs , ys) = cong₂ _,_ (mapᴹ-id M xs) (mapᴹ-id N ys)

    mapᴾ-id : (G : BiPoly) (xs : ⟦ G ⟧ (A , μ F A)) → mapᴾ G xs ≡ xs
    mapᴾ-id (M ∷ G) (inj₁ xs) = cong inj₁ (mapᴹ-id M xs)
    mapᴾ-id (M ∷ G) (inj₂ xs) = cong inj₂ (mapᴾ-id G xs)

    map-id : (x : μ F A) → map x ≡ x
    map-id (con xs) = cong con (mapᴾ-id F xs)

  -- For slides
  -- map-id : (F : BiPoly) {A : Set} (x : μ F A) → map F id x ≡ x

module _ (F : BiPoly) {A B C : Set} (f : B → C) (g : A → B) where

  open Map F

  mutual

    mapᴹ-∘ : (M : BiMono) (xs : ⟦ M ⟧ᴹ (A , μ F A)) → mapᴹ (f ∘ g) M xs ≡ mapᴹ f M (mapᴹ g M xs)
    mapᴹ-∘ ∅       tt        = refl
    mapᴹ-∘ E       a         = refl
    mapᴹ-∘ I       x         = map-∘ x
    mapᴹ-∘ (M ⊗ N) (xs , ys) = cong₂ _,_ (mapᴹ-∘ M xs) (mapᴹ-∘ N ys)

    mapᴾ-∘ : (G : BiPoly) (xs : ⟦ G ⟧ (A , μ F A)) → mapᴾ (f ∘ g) G xs ≡ mapᴾ f G (mapᴾ g G xs)
    mapᴾ-∘ (M ∷ G) (inj₁ xs) = cong inj₁ (mapᴹ-∘ M xs)
    mapᴾ-∘ (M ∷ G) (inj₂ xs) = cong inj₂ (mapᴾ-∘ G xs)

    map-∘ : (x : μ F A) → map (f ∘ g) x ≡ map f (map g x)
    map-∘ (con xs) = cong con (mapᴾ-∘ F xs)

    -- For slides
    -- map-∘ : (F : BiPoly) {A B C : Set} (f : B → C) (g : A → B) (x : μ F A)
    --       → map F (f ∘ g) x ≡ map F f (map F g x)
