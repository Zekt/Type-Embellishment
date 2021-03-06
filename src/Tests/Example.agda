{-# OPTIONS --safe --without-K #-}
open import Prelude

module Tests.Example where

open import Utils.Reflection

open import Generics.Telescope
open import Generics.Description
open import Generics.Recursion
open import Generics.RecursionScheme

open import Generics.Reflection

------------------------------------------------------------------------------
--
`T-Nat : Telescope × Type
`T-Nat = getTelescopeT ℕ

_ : genTel (fst `T-Nat) ≡ω []
_ = refl

_ : evalT (fromTel [] (constTelInfo visible)) ≡ fst `T-Nat
_ = refl

------------------------------------------------------------------------------
--

data Rel (A : Set) : (xs ys : List A) → Set where
`T-rel : Telescope
`T-rel = fst $ getTelescopeT Rel

_ : genTel `T-rel ≡ω [ B ∶ Set ] [ bs ∶ List B ] [ bs ∶ List B ] []
_ = refl

_ : evalT (fromTel ([ A ∶ Set ] [ xs ∶ List A ] [ ys ∶ List A ] []) (constTelInfo visible)) ≡ `T-rel
_ = refl

------------------------------------------------------------------------------
--


-- Okay but unusual examples
sort-is-not-normal : Tel _
sort-is-not-normal = [ b ∶ if true then Bool else ⊥ ] []

`sort-is-not-normal : Telescope
`sort-is-not-normal = evalT (fromTel sort-is-not-normal (constTelInfo visible))

_ : sort-is-not-normal ≡ω [ b ∶ Bool ] []
_ = refl

_ : `sort-is-not-normal ≡ evalT (fromTel ([ b ∶ Bool ] []) (constTelInfo visible))
_ = refl

ex₁ : Bool → Tel _
ex₁ = λ b → []

`ex₁ : Telescope
`ex₁ = evalT (fromTel (Bool ∷ ex₁) (constTelInfo visible))

--
NatD : DataD
NatD = record
  { #levels = 0
  ; applyL  = λ { tt → record
    { alevel  = 0ℓ
    ; Param  = []
    ; Index  = λ _ → []
    ; applyP = λ where
      _ → ι tt
        -- ℕ
        ∷ ρ (ι tt) (ι tt) ∷ []
        -- ℕ → ℕ
    }}
  }

natD' : DataD
natD' = genDataD ℕ

NatT = genDataT NatD ℕ

instance
  NatC : Named (quote ℕ) _
  NatC = named (genDataC NatD NatT)

foldℕP : FoldP
foldℕP = fold-operator (quote ℕ)

unquoteDecl foldℕ = defineFold foldℕP foldℕ

unquoteDecl data Nat constructor z s = defineByDataD NatD Nat (z ∷ s ∷ [])

TreeD : DataD
TreeD = datad 1 λ where
  (ℓ , ⊤) → pdatad ℓ ([ A ∶ Set ℓ ] []) (λ ps → []) λ where
    (A , tt) →
      ι tt
      ∷ (σ[ _ ∶ A ] ρ (ι tt) (ρ (ι tt) (ι tt)))
      ∷ []

data Tree {ℓ : Level} (A : Set ℓ) : Set ℓ where
  leaf : Tree A
  node : (x : A) → Tree A → Tree A → Tree A

-- unquoteDecl data Tree constructor leaf node = defineByDataD TreeD Tree (leaf ∷ node ∷ [])

TreeT = genDataT TreeD Tree
TreeC = genDataC TreeD TreeT
--
ListD : DataD
ListD = record
  { #levels = 1
  ; applyL  = λ { (ℓ , _) → record
    { alevel = ℓ
    ; Param = [ A ∶ Set ℓ ] []
    ; Index = λ _ → []
    ; applyP = λ where
      (A , tt) →
        (ι tt)
        -- List A
        ∷ (σ[ x ∶ A ] (ρ (ι tt) (ι tt)))
        -- (_ : A) → List A → List A
        ∷ []
    }}
  }

ListD' = genDataD List

_ : ListD ≡ω ListD'
_ = refl

-- ListC : DataCᶜ ListD List
ListT = genDataT ListD List
instance 
  ListC : Named (quote List) _
  ListC = named (genDataC ListD ListT)

unquoteDecl data List' constructor nil cons =
  defineByDataD ListD List' (nil ∷ cons ∷ [])

--
data Len (A : Set ℓ) : List A → List A → Set ℓ where
  z : Len A [] []
  s : ∀ {x y xs ys} → (len : Len A xs ys) → Len A (x ∷ xs) (y ∷ ys)

LenD : DataD
DataD.#levels LenD = 1
DataD.applyL  LenD (ℓ , _) = record
  { alevel = ℓ
  ; Param = [ A ∶ Set ℓ ] []
  ; Index = λ where
    (A , tt) → [ xs ∶ List {ℓ} A ] [ ys ∶ List {ℓ} A ] []
  ; applyP = λ where
    (A , tt) →
      ι ([] , [] , tt)
      ∷ σ[ x ∶ A ]
        σ[ y ∶ A ]
        σ[ xs ∶ List A ]
        σ[ ys ∶ List A ] ρ (ι (xs , ys , _)) (ι (x ∷ xs , y ∷ ys , _))
      ∷ []
  }

-- LenC : DataCᶜ LenD Len
LenT = genDataT LenD Len
instance 
  LenC : Named (quote Len) _
  LenC = named (genDataC LenD LenT)
--   dataC
--   (λ { (inl refl) → z {_} {_} ; (inr (inl (x , y , xs , ys , p , refl))) → s {_} {_} {x} {y} {xs} {ys} p })
--   (λ { z → inl refl ; (s {x} {y} {xs} {ys} p) → inr (inl (x , y , xs , ys , p , refl)) })
--   (λ { (inl refl) → refl ; (inr (inl (x , y , xs , ys , p , refl))) → refl })
--   λ { z → refl ; (s x) → refl }

unquoteDecl data Len' constructor newz news =
  defineByDataD LenD Len' (newz ∷ news ∷ [])

newLenD : DataD
newLenD = genDataD Len'

-- translate a translation back
unquoteDecl data newnewLen constructor newnewz newnews =
  defineByDataD newLenD newnewLen (newnewz ∷ newnews ∷ [])

newnewlen : newnewLen ℕ (2 ∷ 5 ∷ []) (1 ∷ 3 ∷ [])
newnewlen = newnews 2 1 [ 5 ] [ 3 ] (newnews 5 3 [] [] newnewz)

--
REL : {a b : Level} → Set a → Set b
    → (ℓ : Level) → Set (a ⊔ b ⊔ lsuc ℓ)
REL A B ℓ = A → B → Set ℓ

data Pointwise {a b ℓ} (A : Set a) (B : Set b) (R : REL A B ℓ) : REL (Maybe A) (Maybe B) (a ⊔ b ⊔ ℓ) where
  just    : ∀ {x y} → R x y → Pointwise A B R (just x) (just y)
  nothing : Pointwise A B R nothing nothing

PointwiseD = genDataD Pointwise
PointwiseT = genDataT PointwiseD Pointwise
PointwiseC = genDataC PointwiseD PointwiseT

unquoteDecl data Pointwise' constructor just' nothing' = defineByDataD PointwiseD Pointwise' (just' ∷ nothing' ∷ [])

{- dataC
  (genToNT List)
  (genFromNT List)
  (genFromN-toNT List)
  -- (λ { (inl refl) → refl ; (inr (inl (x , xs , refl))) → refl })
  (genToN-fromNT List)
  -- (λ { [] → refl ; (x ∷ xs) → refl })
-}

------------------------------------------------------------------------------
-- Data types


data Vec (A : Set ℓ) : ℕ → Set ℓ where
  []  : Vec _ 0
  _∷_ : (x : A) → {n : ℕ} → (xs : Vec A n) → Vec A (suc n)

VecD : DataD
VecD = genDataD Vec
{-
VecD = record
  { #levels = 1
  ; applyL  = λ { (ℓ , tt) → record
    { alevel = ℓ
    ; Param                 = [ A ∶ Set ℓ ] []
    ; Index                 = λ _ → [ _ ∶ ℕ ] []
    ; applyP                = λ where
      (A , tt) →
        ι (zero , tt)
        -- Vec A 0
        ∷ σ[ _ ∶ A ] σ[ n ∶ ℕ ] (ρ (ι (n , tt)) (ι (suc n , tt)))
        -- (x : A) → (n : ℕ) → Vec A n → Vec A (suc n)
        ∷ []
    } }
  }
-}

VecD' : DataD
VecD' = genDataD Vec

-- VecC : DataCᶜ VecD' Vec
VecT = genDataT VecD Vec
VecC = genDataC VecD' VecT

-- generated DataC
VecC′ : DataC VecD' λ { ℓs (A , tt) (n , tt) → Vec A n }
VecC′  = datac
        (λ { {ℓs} {ps} {.(0 , tt)} (inl refl) → []
           ; {ℓs} {ps} {.(suc n , tt)} (inr (inl (x , n , xs , refl)))
               → x ∷ xs
           ; {ℓs} {ps} {is} (inr (inr ()))
           })
        (λ { {ℓs} {ps} {.0 , snd} [] → inl refl
           ; {ℓs} {ps} {suc n , snd} (_∷_ x {.n} xs)
               → inr (inl (x , n , xs , refl))
           })
        (λ { {ℓs} {ps} {.(0 , tt)} (inl refl) → refl
           ; {ℓs} {ps} {.(suc n , tt)} (inr (inl (x , n , xs , refl))) → refl
           ; {ℓs} {ps} {is} (inr (inr ()))
           })
        (λ { {ℓs} {ps} {.0 , snd} [] → refl
           ; {ℓs} {ps} {suc n , snd} (_∷_ x {.n} xs) → refl
           })


unquoteDecl data Vec' constructor nil' cons' = defineByDataD VecD Vec' (nil' ∷ cons' ∷ [])

data _∈_ {ℓ : Level} {A : Set ℓ} : (z : A) (l : List A) → Set ℓ where
  zero : {x : A} {xs : List A} → x ∈ (x ∷ xs)
  suc : {x y : A} {xs : List A} (z : x ∈ xs) → x ∈ (y ∷ xs)

∈D : DataD
∈D = genDataD _∈_

unquoteDecl data ∈' constructor z' s' = defineByDataD ∈D ∈' (z' ∷ s' ∷ [])

data W (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  sup : (x : A) → ((t : B x) → W A B) → W A B

WD : DataD
WD = record
  { #levels = 2
  ; applyL  = λ where
    (ℓ , ℓ' , tt) → record
      { alevel = ℓ ⊔ ℓ'
      ; Param = [ A ∶ Set ℓ ] [ B ∶ (A → Set ℓ') ] []
      ; Index = λ _ → []
      ; applyP = λ where
        (A , B , _) →
          σ[ x ∶ A ] ρ (π[ t ∶ B x ] ι _) (ι _)
          -- (x : A) → ((_ : B x) → W A B) → W A B
          ∷ []
      }
  }


lenP : FoldP
lenP = fold-operator (quote Len)

instance
  _ : Named (quote Pointwise) (DataC PointwiseD PointwiseT)
  _ = named PointwiseC
  
pointwiseP : FoldP
pointwiseP = fold-operator (quote Pointwise)

unquoteDecl foldPW = defineFold pointwiseP foldPW

indℕP : IndP
indℕP = ind-operator (quote ℕ)

unquoteDecl indℕ = defineInd indℕP indℕ

listP : IndP
listP = ind-operator (quote List)

unquoteDecl indList = defineInd listP indList
