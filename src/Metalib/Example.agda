{-# OPTIONS -v meta:5  #-}
open import Prelude
  hiding ([_,_])

module Metalib.Example where

open import Utils.Reflection

open import Generics.Description
open import Generics.Telescope
open import Generics.Recursion
open import Generics.Example

open import Metalib.Telescope
open import Metalib.Datatype
open import Metalib.Recursion

------------------------------------------------------------------------------
-- 
`T-Nat : Telescope × Type
`T-Nat = getTelescopeT ℕ

_ : evalT (fromTelescope $ fst `T-Nat) ≡ []
_ = refl

_ : (evalT (fromTel [])) ≡ (0 , fst `T-Nat)
_ = refl

------------------------------------------------------------------------------
-- 

data Rel (A : Set) : (xs ys : List A) → Set where
`T-rel : Telescope × Type
`T-rel = getTelescopeT Rel

_ : evalT (fromTelescope $ fst `T-rel) ≡ [ B ∶ Set ] [ bs ∶ List B ] [ bs ∶ List B ] []
_ = refl

_ : evalT (fromTel $ [ A ∶ Set ] [ xs ∶ List A ] [ ys ∶ List A ] []) ≡ (3 , fst `T-rel)
_ = refl


------------------------------------------------------------------------------
-- 

data Pointwise (A : Set) (B : Set) (R : A → B → Set) : (xs : List A) → (ys : List B) → Set where 

T-pointwise : Telescope
T-pointwise = fst $ getTelescopeT Pointwise 

_ : evalT (fromTelescope T-pointwise)
  ≡ [ A ∶ Set ] [ B ∶ Set ] [ R ∶ (A → B → Set) ] [ as ∶ List A ] [ bs ∶ List B ] []
_ = refl

_ : evalT (fromTel $ [ A ∶ Set ] [ B ∶ Set ] [ R ∶ (A → B → Set) ] [ xs ∶ List A ] [ ys ∶ List B ] []) ≡ (5 , T-pointwise)
_ = refl

-- Okay but unusual examples
sort-is-not-normal : Tel _
sort-is-not-normal = [ b ∶ if true then Bool else ⊥ ] [] 

`sort-is-not-normal : ℕ × Telescope
`sort-is-not-normal = evalT (fromTel sort-is-not-normal)

_ : sort-is-not-normal ≡ [ b ∶ Bool ] []
_ = refl

_ : `sort-is-not-normal ≢ evalT (fromTel ([ b ∶ Bool ] []))
_ = λ { () }

ex₁ : Bool → Tel _
ex₁ = λ b → []

`ex₁ : ℕ × Telescope
`ex₁ =  evalT (fromTel $ Bool ∷ ex₁)

-- Not really a telescope: 
bad : Tel _
bad = [ b ∶ Bool ] (case b of λ { true → [ n ∶ ℕ ] [] ; false → [] })

data Len (A : Set ℓ) : List A → List A → Set ℓ where
  z : Len A [] []
  s : ∀ {x y xs ys} → Len A xs ys → Len A (x ∷ xs) (y ∷ ys)

LenD : DataD
DataD.#levels LenD = 1
DataD.applyL  LenD (ℓ , _) = record
  { alevel = ℓ
  ; level-pre-fixed-point = refl
  ; Param = [ _ ∶ Set ℓ ] []
  ; Index = λ where
    (A , tt) → [ _ ∶ List {ℓ} A ] [ _ ∶ List {ℓ} A ] []
  ; applyP = λ where
    (A , tt) →
      ι ([] , [] , tt)
      ∷ Σ[ x ∶ A ]
        Σ[ y ∶ A ]
        Σ[ xs ∶ List A ]
        Σ[ ys ∶ List A ] ρ (ι (xs , ys , _)) (ι (x ∷ xs , y ∷ ys , _))
      ∷ []
  }

unquoteDecl data newLen constructor newz news =
  defineByDataD LenD newLen (newz ∷ news ∷ [])

REL : {a b : Level} → Set a → Set b
    → (ℓ : Level) → Set (a ⊔ b ⊔ lsuc ℓ)
REL A B ℓ = A → B → Set ℓ

data Pointwise' {a b ℓ} (A : Set a) (B : Set b) (R : REL A B ℓ) : REL (Maybe A) (Maybe B) (a ⊔ b ⊔ ℓ) where
  just    : ∀ {x y} → R x y → Pointwise' A B R (just x) (just y)
  nothing : Pointwise' A B R nothing nothing

pointwiseD : DataD
DataD.#levels pointwiseD = 3
DataD.applyL  pointwiseD (a , b , ℓ , _) = record
      { alevel = a ⊔ b ⊔ ℓ
      ; level-pre-fixed-point = refl
      ; Param = [ A ∶ Set a ] [ B ∶ Set b ] [ R ∶ REL A B ℓ ] []
      ; Index = λ where
        (A , B , R , _) → [ _ ∶ Maybe A ] [ _ ∶ Maybe B ] []
      ; applyP = λ where
        (A , B , R , _) →
          Σ[ x ∶ A ] Σ[ y ∶ B ] Σ[ _ ∶ R x y ] ι (just x , (just y) , tt)
          ∷ ι (nothing , nothing , tt)
          ∷ []
      }

newLenD : DataD
newLenD = getDataD newLen

natD' : DataD
natD' = getDataD ℕ

-- translate a translation back
unquoteDecl data newnewLen constructor newnewz newnews =
  defineByDataD newLenD newnewLen (newnewz ∷ newnews ∷ [])

newnewlen : newnewLen ℕ (2 ∷ 5 ∷ []) (1 ∷ 3 ∷ [])
newnewlen = newnews 2 1 [ 5 ] [ 3 ] (newnews 5 3 [] [] newnewz)


NatDataC = genDataCT NatD ℕ
PointwiseDataC = genDataCT pointwiseD Pointwise'
--
ListDataC : DataCᶜ ListD List
ListDataC = genDataCT ListD List
{- dataC
  (genToNT List)
  (genFromNT List)
  (genFromN-toNT List)
  -- (λ { (inl refl) → refl ; (inr (inl (x , xs , refl))) → refl })
  (genToN-fromNT List)
  -- (λ { [] → refl ; (x ∷ xs) → refl })
-}
LenDataC : DataCᶜ LenD Len
LenDataC = genDataCT LenD Len 
--   dataC
--   (λ { (inl refl) → z {_} {_} ; (inr (inl (x , y , xs , ys , p , refl))) → s {_} {_} {x} {y} {xs} {ys} p })
--   (λ { z → inl refl ; (s {x} {y} {xs} {ys} p) → inr (inl (x , y , xs , ys , p , refl)) })
--   (λ { (inl refl) → refl ; (inr (inl (x , y , xs , ys , p , refl))) → refl })
--   λ { z → refl ; (s x) → refl }
