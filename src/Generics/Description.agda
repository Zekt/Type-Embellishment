module Generics.Description where

open import Prelude hiding (curry)

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

module _ (I : Set ℓⁱ) where

  {-# NO_UNIVERSE_CHECK #-}
  data RecD : Level → Set where
    ι : (i : I) → RecD lzero
    π : (A : Set ℓʳ) (D : A → RecD ℓʳ') → RecD (ℓʳ ⊔ ℓʳ')

  {-# NO_UNIVERSE_CHECK #-}
  data ConD : Level → Level → ℕ → Set where
    ι : (i : I) → ConD lzero lzero zero
    ρ : (D : RecD ℓʳ) (E : ConD ℓʳ' ℓᵃ' cρ) → ConD (ℓʳ ⊔ ℓʳ') ℓᵃ' (suc cρ)
    σ : (A : Set ℓᵃ) (D : A → ConD ℓʳ' ℓᵃ' cρ) → ConD ℓʳ' (ℓᵃ ⊔ ℓᵃ') cρ

  {-# NO_UNIVERSE_CHECK #-}
  data ConDs : Level → Level → List ℕ → Set where
    ∅   : ConDs lzero lzero []
    _◁_ : (D : ConD ℓʳ ℓᵃ cρ) (Ds : ConDs ℓʳ' ℓᵃ' cρs)
        → ConDs (ℓʳ ⊔ ℓʳ') (ℓᵃ ⊔ ℓᵃ') (cρ ∷ cρs)

  infixr 4 _◁_

{-# NO_UNIVERSE_CHECK #-}
record DataD : Set where
  field
    {plevel} : Level
    {ilevel} : Level
    {rlevel} : Level
    {alevel} : Level
    {recCounts} : List ℕ
  flevel : Level → Level
  flevel ℓ = rlevel ⊔ alevel ⊔ lconds recCounts ℓ ⊔ lcond (length recCounts) ilevel
  field
    level : Level
    level-pre-fixed-point : flevel level ⊔ level ≡ level
    Param : Tel plevel
    Index : ⟦ Param ⟧ᵗ → Tel ilevel
    Desc  : (p : ⟦ Param ⟧ᵗ) → ConDs ⟦ Index p ⟧ᵗ rlevel alevel recCounts

{-# NO_UNIVERSE_CHECK #-}
record UPDataD : Set where
  field
    #levels : ℕ
  Levels : Set
  Levels = Level ^ #levels
  field
    Desc : Levels → DataD

module _ {I : Set ℓⁱ} where

  ⟦_⟧ʳ : RecD I ℓʳ → (I → Set ℓ) → Set (ℓʳ ⊔ ℓ)
  ⟦ ι i   ⟧ʳ X = X i
  ⟦ π A D ⟧ʳ X = (a : A) → ⟦ D a ⟧ʳ X

  ⟦_⟧ᶜ : ConD I ℓʳ ℓᵃ cρ → (I → Set ℓ) → (I → Set (ℓʳ ⊔ ℓᵃ ⊔ lcond cρ ℓ ⊔ ℓⁱ))
  ⟦ ι i   ⟧ᶜ X j = i ≡ j
  ⟦ ρ D E ⟧ᶜ X j = Σ (⟦ D ⟧ʳ X) λ _ → ⟦ E ⟧ᶜ X j
  ⟦ σ A D ⟧ᶜ X j = Σ A λ a → ⟦ D a ⟧ᶜ X j

  ⟦_⟧ᶜˢ : ConDs I ℓʳ ℓᵃ cρs
        → (I → Set ℓ) → (I → Set (ℓʳ ⊔ ℓᵃ ⊔ lconds cρs ℓ ⊔ lcond (length cρs) ℓⁱ))
  ⟦ ∅      ⟧ᶜˢ X i = ⊥
  ⟦ D ◁ Ds ⟧ᶜˢ X i = ⟦ D ⟧ᶜ X i ⊎ ⟦ Ds ⟧ᶜˢ X i

⟦_⟧ᵈ : (D : DataD) (p : ⟦ DataD.Param D ⟧ᵗ)
     → let I = ⟦ DataD.Index D p ⟧ᵗ in (I → Set ℓ) → (I → Set (DataD.flevel D ℓ))
⟦ D ⟧ᵈ p = ⟦ DataD.Desc D p ⟧ᶜˢ

⟦_⟧ᵘᵖᵈ : (D : UPDataD) (ℓs : UPDataD.Levels D) → let Dᵐ = UPDataD.Desc D ℓs in
         (p : ⟦ DataD.Param Dᵐ ⟧ᵗ)
       → let I = ⟦ DataD.Index Dᵐ p ⟧ᵗ in (I → Set ℓ) → (I → Set (DataD.flevel Dᵐ ℓ))
⟦ D ⟧ᵘᵖᵈ ℓs = ⟦ UPDataD.Desc D ℓs ⟧ᵈ

fmapʳ : {I : Set ℓⁱ} (D : RecD I ℓʳ) {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
      → ({i : I} → X i → Y i) → ⟦ D ⟧ʳ X → ⟦ D ⟧ʳ Y
fmapʳ (ι i  ) f x  = f x
fmapʳ (π A D) f xs = λ a → fmapʳ (D a) f (xs a)

fmapᶜ : {I : Set ℓⁱ} (D : ConD I ℓʳ ℓᵃ cρ) {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
      → ({i : I} → X i → Y i) → {i : I} → ⟦ D ⟧ᶜ X i → ⟦ D ⟧ᶜ Y i
fmapᶜ (ι i  ) f eq       = eq
fmapᶜ (ρ D E) f (x , xs) = fmapʳ D f x , fmapᶜ E f xs
fmapᶜ (σ A D) f (a , xs) = a , fmapᶜ (D a) f xs

fmapᶜˢ : {I : Set ℓ} (Ds : ConDs I ℓʳ ℓᵃ cρs) {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
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

append' : ∀ {ℓ ℓ'} → (T : Tel' ℓ) → (⟦ T ⟧ᵗ' → Tel' ℓ') → Tel' (ℓ ⊔ ℓ')
append' ∅       T' = T' tt
append' (A ◁ T) T' = A ◁ λ a → append' (T a) λ t → T' (a , t)

snoc' : ∀ {ℓ ℓ'} → (T : Tel' ℓ) → (⟦ T ⟧ᵗ' → Set ℓ') → Tel' (ℓ ⊔ ℓ')
snoc' ∅       B = B tt ◁ λ _ → ∅
snoc' (A ◁ T) B = A ◁ λ a → snoc' (T a) λ t → B (a , t)

Curried : ∀ {ℓ ℓ'} → (T : Tel' ℓ) → (⟦ T ⟧ᵗ' → Set ℓ') → Set (ℓ ⊔ ℓ')
Curried ∅ X = X tt
Curried (A ◁ T) X = (a : A) → Curried (T a) λ t → X (a , t)

curry : ∀ {ℓ ℓ'} (T : Tel' ℓ) (X : ⟦ T ⟧ᵗ' → Set ℓ') → ((t : ⟦ T ⟧ᵗ') → X t) → Curried T X
curry ∅       X f = f tt
curry (A ◁ T) X f = λ a → curry (T a) (λ t → X (a , t)) (λ t → f (a , t))
