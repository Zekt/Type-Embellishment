module Generics.Description where

open import Prelude hiding (curry)
open import Prelude.List as List

lcond : ℕ → Level → Level
lcond  zero   _ = lzero
lcond (suc n) ℓ = ℓ ⊔ lcond n ℓ

lconds : List ℕ → Level → Level
lconds []       _ = lzero
lconds (n ∷ ns) ℓ = lcond n ℓ ⊔ lconds ns ℓ

lcond-preserves-⊔ : (n : ℕ) (ℓ ℓ' : Level) → lcond n (ℓ ⊔ ℓ') ≡ lcond n ℓ ⊔ lcond n ℓ'
lcond-preserves-⊔  zero   ℓ ℓ' = refl
lcond-preserves-⊔ (suc n) ℓ ℓ' = cong ((ℓ ⊔ ℓ') ⊔_) (lcond-preserves-⊔ n ℓ ℓ')

lcond-upper-bound : (n : ℕ) (ℓ : Level) → lcond n ℓ ⊔ ℓ ≡ ℓ
lcond-upper-bound  zero   ℓ = refl
lcond-upper-bound (suc n) ℓ = lcond-upper-bound n ℓ

lconds-preserves-⊔ : (ns : List ℕ) (ℓ ℓ' : Level)
                   → lconds ns (ℓ ⊔ ℓ') ≡ lconds ns ℓ ⊔ lconds ns ℓ'
lconds-preserves-⊔ []       ℓ ℓ' = refl
lconds-preserves-⊔ (n ∷ ns) ℓ ℓ' = cong₂ _⊔_ (lcond-preserves-⊔ n  ℓ ℓ')
                                            (lconds-preserves-⊔ ns ℓ ℓ')

lconds-upper-bound : (ns : List ℕ) (ℓ : Level) → lconds ns ℓ ⊔ ℓ ≡ ℓ
lconds-upper-bound []       ℓ = refl
lconds-upper-bound (n ∷ ns) ℓ = cong₂ _⊔_ (lcond-upper-bound n  ℓ)
                                         (lconds-upper-bound ns ℓ)

private
  variable
    cρ  : ℕ
    cρs : List ℕ

mutual

  {-# NO_UNIVERSE_CHECK #-}
  data Tel : Level → Set where
    ∅   : Tel lzero
    _▷_ : (T : Tel ℓ) (A : ⟦ T ⟧ᵗ → Set ℓ') → Tel (ℓ ⊔ ℓ')

  ⟦_⟧ᵗ : Tel ℓ → Set ℓ
  ⟦ ∅     ⟧ᵗ = ⊤
  ⟦ T ▷ A ⟧ᵗ = Σ ⟦ T ⟧ᵗ A

infixl 4 _▷_

RecB : Set
RecB = List Level

ConB : Set
ConB = List (Level ⊎ RecB)

ConBs : Set
ConBs = List ConB

max-ℓ : List Level → Level
max-ℓ = foldr _⊔_ lzero

maxMap : {A : Set} → (A → Level) → List A → Level
maxMap f = max-ℓ ∘ List.map f

ρ-level : Level ⊎ RecB → Level
ρ-level (inl _ ) = lzero
ρ-level (inr rb) = max-ℓ rb

has-ρ? : Level → Level ⊎ RecB → Level
has-ρ? ℓ (inl _) = lzero
has-ρ? ℓ (inr _) = ℓ

σ-level : Level ⊎ RecB → Level
σ-level (inl ℓ) = ℓ
σ-level (inr _) = lzero

max-π : ConB → Level
max-π = maxMap ρ-level

max-σ : ConB → Level
max-σ = maxMap σ-level

hasRec? : Level → ConB → Level
hasRec? ℓ = maxMap (has-ρ? ℓ)

hasCon? : Level → ConBs → Level
hasCon? ℓ = maxMap (λ _ → ℓ)

maxMap-dist-⊔ : {A : Set} (f g : A → Level) (as : List A)
              → maxMap (λ a → f a ⊔ g a) as ≡ maxMap f as ⊔ maxMap g as
maxMap-dist-⊔ f g []       = refl
maxMap-dist-⊔ f g (a ∷ as) = cong (f a ⊔ g a ⊔_) (maxMap-dist-⊔ f g as)

maxMap-bound : {A : Set} (f : A → Level) (ℓ : Level)
             → (∀ a → f a ⊔ ℓ ≡ ℓ) → ∀ as → maxMap f as ⊔ ℓ ≡ ℓ
maxMap-bound f ℓ eq []       = refl
maxMap-bound f ℓ eq (a ∷ as) = cong₂ _⊔_ (eq a) (maxMap-bound f ℓ eq as)

hasRec?-bound : ∀ ℓ cb → hasRec? ℓ cb ⊔ ℓ ≡ ℓ
hasRec?-bound ℓ []            = refl
hasRec?-bound ℓ (inl ℓ' ∷ cb) = hasRec?-bound ℓ cb
hasRec?-bound ℓ (inr rb ∷ cb) = hasRec?-bound ℓ cb

hasRec?-dist-⊔ : ∀ ℓ ℓ' cb → hasRec? (ℓ ⊔ ℓ') cb ≡ hasRec? ℓ cb ⊔ hasRec? ℓ' cb
hasRec?-dist-⊔ ℓ ℓ' []             = refl
hasRec?-dist-⊔ ℓ ℓ' (inl ℓ'' ∷ cb) = hasRec?-dist-⊔ ℓ ℓ' cb
hasRec?-dist-⊔ ℓ ℓ' (inr rb  ∷ cb) = cong (ℓ ⊔ ℓ' ⊔_) (hasRec?-dist-⊔ ℓ ℓ' cb)

hasCon?-bound : ∀ ℓ cbs → hasCon? ℓ cbs ⊔ ℓ ≡ ℓ
hasCon?-bound ℓ []        = refl
hasCon?-bound ℓ (_ ∷ cbs) = hasCon?-bound ℓ cbs

hasCon?-dist-⊔ : ∀ ℓ ℓ' cbs → hasCon? (ℓ ⊔ ℓ') cbs ≡ hasCon? ℓ cbs ⊔ hasCon? ℓ' cbs
hasCon?-dist-⊔ ℓ ℓ' []        = refl
hasCon?-dist-⊔ ℓ ℓ' (_ ∷ cbs) = cong (ℓ ⊔ ℓ' ⊔_) (hasCon?-dist-⊔ ℓ ℓ' cbs)

maxMap-hasRec?≤hasCon? : ∀ ℓ cbs → maxMap (hasRec? ℓ) cbs ⊔ hasCon? ℓ cbs ≡ hasCon? ℓ cbs
maxMap-hasRec?≤hasCon? ℓ []         = refl
maxMap-hasRec?≤hasCon? ℓ (cb ∷ cbs) = cong₂ _⊔_ (hasRec?-bound ℓ cb)
                                                (maxMap-hasRec?≤hasCon? ℓ cbs)

private variable
    rb  : RecB
    cb  : ConB
    cbs : ConBs

module _ (I : Set ℓⁱ) where

  {-# NO_UNIVERSE_CHECK #-}
  data RecD : RecB → Set where
    ι : (i : I) → RecD []
    π : (A : Set ℓ) (D : A → RecD rb) → RecD (ℓ ∷ rb)

  {-# NO_UNIVERSE_CHECK #-}
  data ConD : ConB → Set where
    ι : (i : I) → ConD []
    σ : (A : Set ℓ) (D : A → ConD cb) → ConD (inl ℓ  ∷ cb)
    ρ : (D : RecD rb) (E : ConD cb)   → ConD (inr rb ∷ cb)

  {-# NO_UNIVERSE_CHECK #-}
  data ConDs : ConBs → Set where
    ∅   : ConDs []
    _◁_ : (D : ConD cb) (Ds : ConDs cbs) → ConDs (cb ∷ cbs)

  infixr 4 _◁_

{-# NO_UNIVERSE_CHECK #-}
record DataD : Set where
  field
    {plevel} : Level
    {ilevel} : Level
    {struct} : ConBs
  flevel : Level → Level
  flevel ℓ = maxMap max-π struct ⊔ maxMap max-σ struct ⊔
             maxMap (hasRec? ℓ) struct ⊔ hasCon? ilevel struct
  field
    level : Level
    level-pre-fixed-point : flevel level ⊔ level ≡ level
    Param : Tel plevel
    Index : ⟦ Param ⟧ᵗ → Tel ilevel
    Desc  : (p : ⟦ Param ⟧ᵗ) → ConDs ⟦ Index p ⟧ᵗ struct

{-# NO_UNIVERSE_CHECK #-}
record UPDataD : Set where
  field
    #levels : ℕ
  Levels : Set
  Levels = Level ^ #levels
  field
    Desc : Levels → DataD

module _ {I : Set ℓⁱ} where

  ⟦_⟧ʳ : RecD I rb → (I → Set ℓ) → Set (max-ℓ rb ⊔ ℓ)
  ⟦ ι i   ⟧ʳ X = X i
  ⟦ π A D ⟧ʳ X = (a : A) → ⟦ D a ⟧ʳ X

  ⟦_⟧ᶜ : ConD I cb → (I → Set ℓ) → (I → Set (max-π cb ⊔ max-σ cb ⊔ hasRec? ℓ cb ⊔ ℓⁱ))
  ⟦ ι i   ⟧ᶜ X j = i ≡ j
  ⟦ σ A D ⟧ᶜ X j = Σ A λ a → ⟦ D a ⟧ᶜ X j
  ⟦ ρ D E ⟧ᶜ X j = Σ (⟦ D ⟧ʳ X) λ _ → ⟦ E ⟧ᶜ X j

  ⟦_⟧ᶜˢ : ConDs I cbs → (I → Set ℓ) → (I → Set (maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔
                                                maxMap (hasRec? ℓ) cbs ⊔ hasCon? ℓⁱ cbs))
  ⟦ ∅      ⟧ᶜˢ X i = ⊥
  ⟦ D ◁ Ds ⟧ᶜˢ X i = ⟦ D ⟧ᶜ X i ⊎ ⟦ Ds ⟧ᶜˢ X i

⟦_⟧ᵈ : (D : DataD) (p : ⟦ DataD.Param D ⟧ᵗ)
     → let I = ⟦ DataD.Index D p ⟧ᵗ in (I → Set ℓ) → (I → Set (DataD.flevel D ℓ))
⟦ D ⟧ᵈ p = ⟦ DataD.Desc D p ⟧ᶜˢ

⟦_⟧ᵘᵖᵈ : (D : UPDataD) (ℓs : UPDataD.Levels D) → let Dᵐ = UPDataD.Desc D ℓs in
         (p : ⟦ DataD.Param Dᵐ ⟧ᵗ)
       → let I = ⟦ DataD.Index Dᵐ p ⟧ᵗ in (I → Set ℓ) → (I → Set (DataD.flevel Dᵐ ℓ))
⟦ D ⟧ᵘᵖᵈ ℓs = ⟦ UPDataD.Desc D ℓs ⟧ᵈ

fmapʳ : {I : Set ℓⁱ} (D : RecD I rb) {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
      → ({i : I} → X i → Y i) → ⟦ D ⟧ʳ X → ⟦ D ⟧ʳ Y
fmapʳ (ι i  ) f x  = f x
fmapʳ (π A D) f xs = λ a → fmapʳ (D a) f (xs a)

fmapᶜ : {I : Set ℓⁱ} (D : ConD I cb) {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
      → ({i : I} → X i → Y i) → {i : I} → ⟦ D ⟧ᶜ X i → ⟦ D ⟧ᶜ Y i
fmapᶜ (ι i  ) f eq       = eq
fmapᶜ (σ A D) f (a , xs) = a , fmapᶜ (D a) f xs
fmapᶜ (ρ D E) f (x , xs) = fmapʳ D f x , fmapᶜ E f xs

fmapᶜˢ : {I : Set ℓ} (Ds : ConDs I cbs) {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
       → ({i : I} → X i → Y i) → {i : I} → ⟦ Ds ⟧ᶜˢ X i → ⟦ Ds ⟧ᶜˢ Y i
fmapᶜˢ (D ◁ Ds) f (inl xs) = inl (fmapᶜ  D  f xs)
fmapᶜˢ (D ◁ Ds) f (inr xs) = inr (fmapᶜˢ Ds f xs)

fmapᵈ : (D : DataD) (p : ⟦ DataD.Param D ⟧ᵗ) → let I = ⟦ DataD.Index D p ⟧ᵗ in
        {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
      → ({i : I} → X i → Y i) → {i : I} → ⟦ D ⟧ᵈ p X i → ⟦ D ⟧ᵈ p Y i
fmapᵈ D p = fmapᶜˢ (DataD.Desc D p)

fmapᵘᵖᵈ : (D : UPDataD) (ℓs : UPDataD.Levels D) → let Dᵐ = UPDataD.Desc D ℓs in
        (p : ⟦ DataD.Param Dᵐ ⟧ᵗ) → let I = ⟦ DataD.Index Dᵐ p ⟧ᵗ in
        {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
      → ({i : I} → X i → Y i) → {i : I} → ⟦ D ⟧ᵘᵖᵈ ℓs p X i → ⟦ D ⟧ᵘᵖᵈ ℓs p Y i
fmapᵘᵖᵈ D ℓs = fmapᵈ (UPDataD.Desc D ℓs)

{-# NO_UNIVERSE_CHECK #-}
data Tel' : Level → Set where
  ∅   : Tel' lzero
  _◁_ : ∀ {ℓ ℓ'} (A : Set ℓ) (T : A → Tel' ℓ') → Tel' (ℓ ⊔ ℓ')

⟦_⟧ᵗ' : ∀ {ℓ} → Tel' ℓ → Set ℓ
⟦ ∅     ⟧ᵗ' = ⊤
⟦ A ◁ T ⟧ᵗ' = Σ A λ a → ⟦ T a ⟧ᵗ'

-- de Bruijn's notation 

◁-syntax : (A : Set ℓ) (T : A → Tel' ℓ') → Tel' (ℓ ⊔ ℓ')
◁-syntax = _◁_

syntax ◁-syntax A (λ x → T) = [ x ∶ A ] T

append' : (T : Tel' ℓ) → (⟦ T ⟧ᵗ' → Tel' ℓ') → Tel' (ℓ ⊔ ℓ')
append' ∅       T' = T' tt
append' (A ◁ T) T' = A ◁ λ a → append' (T a) λ t → T' (a , t)

snoc' : (T : Tel' ℓ) → (⟦ T ⟧ᵗ' → Set ℓ') → Tel' (ℓ ⊔ ℓ')
snoc' ∅       B = B tt ◁ λ _ → ∅
snoc' (A ◁ T) B = A ◁ λ a → snoc' (T a) λ t → B (a , t)

Curried : (T : Tel' ℓ) → (⟦ T ⟧ᵗ' → Set ℓ') → Set (ℓ ⊔ ℓ')
Curried ∅ X = X tt
Curried (A ◁ T) X = (a : A) → Curried (T a) λ t → X (a , t)

curry : (T : Tel' ℓ) (X : ⟦ T ⟧ᵗ' → Set ℓ') → ((t : ⟦ T ⟧ᵗ') → X t) → Curried T X
curry ∅       X f = f tt
curry (A ◁ T) X f = λ a → curry (T a) (λ t → X (a , t)) (λ t → f (a , t))
