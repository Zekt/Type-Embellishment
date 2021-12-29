{-# OPTIONS --safe --without-K #-}

module Generics.Safe.Telescope where

open import Prelude

infixr 5 _∷_

data Tel : Level → Setω where
  []  : Tel lzero
  _∷_ : (A : Set ℓ) (T : A → Tel ℓ') → Tel (ℓ ⊔ ℓ')

-- de Bruijn's notation

∷-syntax : (A : Set ℓ) (T : A → Tel ℓ') → Tel (ℓ ⊔ ℓ')
∷-syntax = _∷_

syntax ∷-syntax A (λ x → T) = [ x ∶ A ] T

⟦_⟧ᵗ : Tel ℓ → Set ℓ
⟦ []    ⟧ᵗ = ⊤
⟦ A ∷ T ⟧ᵗ = Σ A λ a → ⟦ T a ⟧ᵗ

record ∀ᵗ (visible : Bool) {ℓ ℓ'} (T : Tel ℓ) (X : ⟦ T ⟧ᵗ → Set ℓ') : Set (ℓ ⊔ ℓ') where
  field _$$_ : (t : ⟦ T ⟧ᵗ) → X t
  infixl -100 _$$_

Curriedᵗ : (visible : Bool) (T : Tel ℓ) → (⟦ T ⟧ᵗ → Set ℓ') → Set (ℓ ⊔ ℓ')
Curriedᵗ _     []      X = X tt
Curriedᵗ false (A ∷ T) X = {a : A} → Curriedᵗ false (T a) (curry X a)
Curriedᵗ true  (A ∷ T) X = (a : A) → Curriedᵗ true  (T a) (curry X a)

curryᵗ : (T : Tel ℓ) (X : ⟦ T ⟧ᵗ → Set ℓ') {visible : Bool}
       → ((t : ⟦ T ⟧ᵗ) → X t) → Curriedᵗ visible T X
curryᵗ []      X         f = f tt
curryᵗ (A ∷ T) X {false} f =       curryᵗ (T _) (curry X _) (curry f _)
curryᵗ (A ∷ T) X {true } f = λ a → curryᵗ (T a) (curry X a) (curry f a)

uncurryᵗ : (T : Tel ℓ) (X : ⟦ T ⟧ᵗ → Set ℓ') {visible : Bool}
         → Curriedᵗ visible T X → (t : ⟦ T ⟧ᵗ) → X t
uncurryᵗ []      X         f tt      = f
uncurryᵗ (A ∷ T) X {false} f (a , t) = uncurryᵗ (T a) (curry X a)  f    t
uncurryᵗ (A ∷ T) X {true } f (a , t) = uncurryᵗ (T a) (curry X a) (f a) t

snocᵗ : (T : Tel ℓ) → (⟦ T ⟧ᵗ → Set ℓ') → Tel (ℓ ⊔ ℓ')
snocᵗ []      B = B tt ∷ λ _ → []
snocᵗ (A ∷ T) B = A ∷ λ a → snocᵗ (T a) (curry B a)

snocᵗ-inj : {T : Tel ℓ} {A : ⟦ T ⟧ᵗ → Set ℓ'} → Σ ⟦ T ⟧ᵗ A → ⟦ snocᵗ T A ⟧ᵗ
snocᵗ-inj {T = []   } (_       , a) = a , tt
snocᵗ-inj {T = B ∷ T} ((b , t) , a) = b , snocᵗ-inj {T = T b} (t , a)

snocᵗ-proj : {T : Tel ℓ} {A : ⟦ T ⟧ᵗ → Set ℓ'} → ⟦ snocᵗ T A ⟧ᵗ → Σ ⟦ T ⟧ᵗ A
snocᵗ-proj {T = []   } (a , _) = tt , a
snocᵗ-proj {T = B ∷ T} (b , t) = let (t' , a) = snocᵗ-proj {T = T b} t in ((b , t') , a)

snocᵗ-proj-inj : {T : Tel ℓ} {A : ⟦ T ⟧ᵗ → Set ℓ'}
                 (p : Σ ⟦ T ⟧ᵗ A) → snocᵗ-proj (snocᵗ-inj p) ≡ p
snocᵗ-proj-inj {T = []   } (_       , a) = refl
snocᵗ-proj-inj {T = B ∷ T} ((b , t) , a) = cong (λ p → let (t , a) = p in (b , t) , a)
                                                (snocᵗ-proj-inj {T = T b} (t , a))

snoc²ᵗ : (T : Tel ℓ) → (⟦ T ⟧ᵗ → Set ℓ') → (⟦ T ⟧ᵗ → Set ℓ'') → Tel (ℓ ⊔ ℓ' ⊔ ℓ'')
snoc²ᵗ []      B C = B tt ∷ λ _ → C tt ∷ λ _ → []
snoc²ᵗ (A ∷ T) B C = A ∷ λ a → snoc²ᵗ (T a) (curry B a) (curry C a)

snoc²ᵗ-inj : {T : Tel ℓ} {B : ⟦ T ⟧ᵗ → Set ℓ'} {C : ⟦ T ⟧ᵗ → Set ℓ''}
           → Σ[ t ∈ ⟦ T ⟧ᵗ ] B t × C t → ⟦ snoc²ᵗ T B C ⟧ᵗ
snoc²ᵗ-inj {T = []   } (_       , b , c) = b , c , tt
snoc²ᵗ-inj {T = A ∷ T} ((a , t) , b , c) = a , snoc²ᵗ-inj {T = T a} (t , b , c)

snoc²ᵗ-proj : {T : Tel ℓ} {B : ⟦ T ⟧ᵗ → Set ℓ'} {C : ⟦ T ⟧ᵗ → Set ℓ''}
            → ⟦ snoc²ᵗ T B C ⟧ᵗ → Σ[ t ∈ ⟦ T ⟧ᵗ ] B t × C t
snoc²ᵗ-proj {T = []   } (b , c , _) = tt , b , c
snoc²ᵗ-proj {T = A ∷ T} (a , t) = let (t' , b , c) = snoc²ᵗ-proj {T = T a} t
                                  in  ((a , t') , b , c)

snoc²ᵗ-proj-inj : {T : Tel ℓ} {B : ⟦ T ⟧ᵗ → Set ℓ'} {C : ⟦ T ⟧ᵗ → Set ℓ''}
                 (p : Σ[ t ∈ ⟦ T ⟧ᵗ ] B t × C t) → snoc²ᵗ-proj (snoc²ᵗ-inj p) ≡ p
snoc²ᵗ-proj-inj {T = []   } (_       , b , c) = refl
snoc²ᵗ-proj-inj {T = A ∷ T} ((a , t) , b , c) =
  cong (λ p → let (t , b , c) = p in (a , t) , b , c)
       (snoc²ᵗ-proj-inj {T = T a} (t , b , c))

_++_ : (T : Tel ℓ) → (⟦ T ⟧ᵗ → Tel ℓ') → Tel (ℓ ⊔ ℓ')
_++_ []      U = U tt
_++_ (A ∷ T) U = A ∷ λ a → T a ++ λ t → U (a , t)

_^_ : Set → ℕ → Set
A ^ zero  = ⊤
A ^ suc n = A × (A ^ n)

record ∀ℓ (n : ℕ) {ℓf : Level ^ n → Level}
  (X : (ℓs : Level ^ n) → Set (ℓf ℓs)) : Setω where
  field _$$_ : (ℓs : Level ^ n) → X ℓs
  infixl -100 _$$_

record ∀ℓω (n : ℕ) (X : Level ^ n → Setω) : Setω where
  field _$$_ : (ℓs : Level ^ n) → X ℓs
  infixl -100 _$$_
