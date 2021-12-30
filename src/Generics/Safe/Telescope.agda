{-# OPTIONS --safe --without-K #-}

module Generics.Safe.Telescope where

open import Prelude

infixr 5 _∷_

data Tel : Level → Setω where
  []  : Tel lzero
  _∷_ : (A : Set ℓ) (T : A → Tel ℓ') → Tel (ℓ ⊔ ℓ')

-- de Bruijn's notation

∷-syntaxᵗ : (A : Set ℓ) (T : A → Tel ℓ') → Tel (ℓ ⊔ ℓ')
∷-syntaxᵗ = _∷_

syntax ∷-syntaxᵗ A (λ x → T) = [ x ∶ A ] T

⟦_⟧ᵗ : Tel ℓ → Set ℓ
⟦ []    ⟧ᵗ = ⊤
⟦ A ∷ T ⟧ᵗ = Σ A λ a → ⟦ T a ⟧ᵗ

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

_++_ : (T : Tel ℓ) → (⟦ T ⟧ᵗ → Tel ℓ') → Tel (ℓ ⊔ ℓ')
_++_ []      U = U tt
_++_ (A ∷ T) U = A ∷ λ a → T a ++ λ t → U (a , t)

append-proj : (T : Tel ℓ) (U : ⟦ T ⟧ᵗ → Tel ℓ') → ⟦ T ++ U ⟧ᵗ → Σ ⟦ T ⟧ᵗ λ t → ⟦ U t ⟧ᵗ
append-proj []      U u        = tt , u
append-proj (A ∷ T) U (a , tu) =
 let (t , u) = append-proj (T a) (λ t → U (a , t)) tu in  (a , t) , u

infixl 5 _▷_

mutual

  data BTel : Level → Setω where
    []  : BTel lzero
    _∷_ : (A : Set ℓ) (T : A → BTel ℓ') → BTel (ℓ ⊔ ℓ')
    _▷_ : (T : BTel ℓ) (A : ⟦ T ⟧ᵇᵗ → Set ℓ') → BTel (ℓ ⊔ ℓ')

  ⟦_⟧ᵇᵗ : BTel ℓ → Set ℓ
  ⟦ []    ⟧ᵇᵗ = ⊤
  ⟦ A ∷ T ⟧ᵇᵗ = Σ A λ a → ⟦ T a ⟧ᵇᵗ
  ⟦ T ▷ A ⟧ᵇᵗ = Σ ⟦ T ⟧ᵇᵗ A

∷-syntaxᵇᵗ : (A : Set ℓ) (T : A → BTel ℓ') → BTel (ℓ ⊔ ℓ')
∷-syntaxᵇᵗ = _∷_

syntax ∷-syntaxᵇᵗ A (λ x → T) = [ x ∶ A ] T

toBTel : Tel ℓ → BTel ℓ
toBTel []      = []
toBTel (A ∷ T) = A ∷ λ a → toBTel (T a)

mutual

  fromBTel : BTel ℓ → Tel ℓ
  fromBTel []      = []
  fromBTel (A ∷ T) = A ∷ λ a → fromBTel (T a)
  fromBTel (T ▷ A) = fromBTel T ++ λ t → A (fromBTel-proj T t) ∷ λ _ → []

  fromBTel-proj : (T : BTel ℓ) → ⟦ fromBTel T ⟧ᵗ → ⟦ T ⟧ᵇᵗ
  fromBTel-proj []      _       = tt
  fromBTel-proj (A ∷ T) (a , t) = a , fromBTel-proj (T a) t
  fromBTel-proj (T ▷ A) ta      =
    let (t , a , _) = append-proj (fromBTel T) _ ta in fromBTel-proj T t , a

Curriedᵇᵗ : (visible : Bool) (T : BTel ℓ) (X : ⟦ T ⟧ᵇᵗ → Set ℓ') → Set (ℓ ⊔ ℓ')
Curriedᵇᵗ _     []      X = X tt
Curriedᵇᵗ false (A ∷ T) X = {a : A} → Curriedᵇᵗ false (T a) (curry X a)
Curriedᵇᵗ true  (A ∷ T) X = (a : A) → Curriedᵇᵗ true  (T a) (curry X a)
Curriedᵇᵗ false (T ▷ A) X = Curriedᵇᵗ false T λ t → {a : A t} → X (t , a)
Curriedᵇᵗ true  (T ▷ A) X = Curriedᵇᵗ true  T λ t → (a : A t) → X (t , a)

curryᵇᵗ : (T : BTel ℓ) (X : ⟦ T ⟧ᵇᵗ → Set ℓ') {visible : Bool}
        → ((t : ⟦ T ⟧ᵇᵗ) → X t) → Curriedᵇᵗ visible T X
curryᵇᵗ []      X         f = f tt
curryᵇᵗ (A ∷ T) X {false} f =       curryᵇᵗ (T _) (curry X _) (curry f _)
curryᵇᵗ (A ∷ T) X {true } f = λ a → curryᵇᵗ (T a) (curry X a) (curry f a)
curryᵇᵗ (T ▷ A) X {false} f = curryᵇᵗ T _ λ t {a} → f (t , a)
curryᵇᵗ (T ▷ A) X {true } f = curryᵇᵗ T _ λ t  a  → f (t , a)

uncurryᵇᵗ : (T : BTel ℓ) (X : ⟦ T ⟧ᵇᵗ → Set ℓ') {visible : Bool}
          → Curriedᵇᵗ visible T X → (t : ⟦ T ⟧ᵇᵗ) → X t
uncurryᵇᵗ []      X         f tt      = f
uncurryᵇᵗ (A ∷ T) X {false} f (a , t) = uncurryᵇᵗ (T a) (curry X a)  f    t
uncurryᵇᵗ (A ∷ T) X {true } f (a , t) = uncurryᵇᵗ (T a) (curry X a) (f a) t
uncurryᵇᵗ (T ▷ A) X {false} f (t , a) = uncurryᵇᵗ T _ f t {a}
uncurryᵇᵗ (T ▷ A) X {true } f (t , a) = uncurryᵇᵗ T _ f t  a

_^_ : Set → ℕ → Set
A ^ zero  = ⊤
A ^ suc n = A × (A ^ n)

record ∀ᵗ (visible : Bool) {ℓ ℓ'} (T : Tel ℓ) (X : ⟦ T ⟧ᵗ → Set ℓ') : Set (ℓ ⊔ ℓ') where
  field _$$_ : (t : ⟦ T ⟧ᵗ) → X t
  infixl -100 _$$_

record ∀ᵇᵗ (visible : Bool) {ℓ ℓ'} (T : BTel ℓ) (X : ⟦ T ⟧ᵇᵗ → Set ℓ') : Set (ℓ ⊔ ℓ') where
  field _$$_ : (t : ⟦ T ⟧ᵇᵗ) → X t
  infixl -100 _$$_

record ∀ℓ (n : ℕ) {ℓf : Level ^ n → Level} (X : (ℓs : Level ^ n) → Set (ℓf ℓs)) : Setω where
  field _$$_ : (ℓs : Level ^ n) → X ℓs
  infixl -100 _$$_

record ∀ℓω (n : ℕ) (X : Level ^ n → Setω) : Setω where
  field _$$_ : (ℓs : Level ^ n) → X ℓs
  infixl -100 _$$_
