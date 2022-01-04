{-# OPTIONS --without-K #-}

open import Prelude

module Generics.Telescope where

infixr 5 _∷_

{-# NO_UNIVERSE_CHECK #-}
data Tel : Level → Set where
  []  : Tel lzero
  _∷_ : (A : Set ℓ) (T : A → Tel ℓ') → Tel (ℓ ⊔ ℓ')

-- de Bruijn's notation

∷-syntax : (A : Set ℓ) (T : A → Tel ℓ') → Tel (ℓ ⊔ ℓ')
∷-syntax = _∷_

syntax ∷-syntax A (λ x → T) = [ x ∶ A ] T

⟦_⟧ᵗ : Tel ℓ → Set ℓ
⟦ []    ⟧ᵗ = ⊤
⟦ A ∷ T ⟧ᵗ = Σ A λ a → ⟦ T a ⟧ᵗ

infixr 5 _++ᵗ_
_++ᵗ_ : (T : Tel ℓ) → (⟦ T ⟧ᵗ → Tel ℓ') → Tel (ℓ ⊔ ℓ')
_++ᵗ_ []      U = U tt
_++ᵗ_ (A ∷ T) U = A ∷ λ a → T a ++ᵗ λ t → U (a , t)

appendᵗ-proj : (T : Tel ℓ) (U : ⟦ T ⟧ᵗ → Tel ℓ') → ⟦ T ++ᵗ U ⟧ᵗ → Σ ⟦ T ⟧ᵗ λ t → ⟦ U t ⟧ᵗ
appendᵗ-proj []      U u        = tt , u
appendᵗ-proj (A ∷ T) U (a , tu) =
  let (t , u) = appendᵗ-proj (T a) (λ t → U (a , t)) tu in  (a , t) , u

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

_^_ : Set → ℕ → Set
A ^ zero  = ⊤
A ^ suc n = A × (A ^ n)

{-# NO_UNIVERSE_CHECK #-}
data MTel : Level → Set

⟦_⟧ᵐᵗ : MTel ℓ → Set ℓ

data MTel where
    []   : MTel lzero
    _∷_  : (A : Set ℓ) (T : A → MTel ℓ') → MTel (ℓ ⊔ ℓ')
    _++_ : (T : MTel ℓ) (U : ⟦ T ⟧ᵐᵗ → MTel ℓ') → MTel (ℓ ⊔ ℓ')

⟦ []    ⟧ᵐᵗ = ⊤
⟦ A ∷  T ⟧ᵐᵗ = Σ A λ a → ⟦ T a ⟧ᵐᵗ
⟦ T ++ U ⟧ᵐᵗ = Σ ⟦ T ⟧ᵐᵗ λ t → ⟦ U t ⟧ᵐᵗ

∷-syntaxᵐᵗ : (A : Set ℓ) (T : A → MTel ℓ') → MTel (ℓ ⊔ ℓ')
∷-syntaxᵐᵗ = _∷_

syntax ∷-syntaxᵐᵗ A (λ x → T) = [ x ∶ A ] T

toMTel : ∀ {ℓ} → Tel ℓ → MTel ℓ
toMTel []      = []
toMTel (A ∷ T) = A ∷ λ a → toMTel (T a)

mutual

  fromMTel : MTel ℓ → Tel ℓ
  fromMTel []       = []
  fromMTel (A ∷  T) = A ∷ λ a → fromMTel (T a)
  fromMTel (T ++ U) = fromMTel T ++ᵗ λ t → fromMTel (U (fromMTel-proj T t))

  fromMTel-proj : (T : MTel ℓ) → ⟦ fromMTel T ⟧ᵗ → ⟦ T ⟧ᵐᵗ
  fromMTel-proj []       _       = tt
  fromMTel-proj (A ∷  T) (a , t) = a , fromMTel-proj (T a) t
  fromMTel-proj (T ++ U) tu      =
    let (t , u) = appendᵗ-proj (fromMTel T) _ tu in fromMTel-proj T t , fromMTel-proj _ u

Curriedᵐᵗ : (visible : Bool) (T : MTel ℓ) (X : ⟦ T ⟧ᵐᵗ → Set ℓ') → Set (ℓ ⊔ ℓ')
Curriedᵐᵗ _     []       X = X tt
Curriedᵐᵗ false (A ∷  T) X = {a : A} → Curriedᵐᵗ false (T a) (curry X a)
Curriedᵐᵗ true  (A ∷  T) X = (a : A) → Curriedᵐᵗ true  (T a) (curry X a)
Curriedᵐᵗ v     (T ++ U) X = Curriedᵐᵗ v T λ t → Curriedᵐᵗ v (U t) λ u → X (t , u)

curryᵐᵗ : (T : MTel ℓ) (X : ⟦ T ⟧ᵐᵗ → Set ℓ') {visible : Bool}
        → ((t : ⟦ T ⟧ᵐᵗ) → X t) → Curriedᵐᵗ visible T X
curryᵐᵗ []       X         f = f tt
curryᵐᵗ (A ∷  T) X {false} f =       curryᵐᵗ (T _) (curry X _) (curry f _)
curryᵐᵗ (A ∷  T) X {true } f = λ a → curryᵐᵗ (T a) (curry X a) (curry f a)
curryᵐᵗ (T ++ U) X         f = curryᵐᵗ T _ λ t → curryᵐᵗ (U t) _ λ u → f (t , u)

uncurryᵐᵗ : (T : MTel ℓ) (X : ⟦ T ⟧ᵐᵗ → Set ℓ') {visible : Bool}
          → Curriedᵐᵗ visible T X → (t : ⟦ T ⟧ᵐᵗ) → X t
uncurryᵐᵗ []       X         f tt      = f
uncurryᵐᵗ (A ∷  T) X {false} f (a , t) = uncurryᵐᵗ (T a) (curry X a)  f    t
uncurryᵐᵗ (A ∷  T) X {true } f (a , t) = uncurryᵐᵗ (T a) (curry X a) (f a) t
uncurryᵐᵗ (T ++ U) X         f (t , u) = uncurryᵐᵗ (U t) _ (uncurryᵐᵗ T _ f t) u

record ∀ᵗ (visible : Bool) {ℓ ℓ'} (T : Tel ℓ) (X : ⟦ T ⟧ᵗ → Set ℓ') : Set (ℓ ⊔ ℓ') where
  field _$$_ : (t : ⟦ T ⟧ᵗ) → X t
  infixl -100 _$$_

record ∀ᵐᵗ (visible : Bool) {ℓ ℓ'} (T : MTel ℓ) (X : ⟦ T ⟧ᵐᵗ → Set ℓ') : Set (ℓ ⊔ ℓ') where
  field _$$_ : (t : ⟦ T ⟧ᵐᵗ) → X t
  infixl -100 _$$_

record ∀ℓ (n : ℕ) {ℓf : Level ^ n → Level} (X : (ℓs : Level ^ n) → Set (ℓf ℓs)) : Setω where
  field _$$_ : (ℓs : Level ^ n) → X ℓs
  infixl -100 _$$_

record ∀ℓω (n : ℕ) (X : Level ^ n → Setω) : Setω where
  field _$$_ : (ℓs : Level ^ n) → X ℓs
  infixl -100 _$$_
