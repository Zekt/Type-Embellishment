{-# OPTIONS --safe --without-K #-}

open import Prelude

module Generics.Telescope where

open import Agda.Builtin.Reflection public using (Visibility; visible; hidden; instance′)

infixr 5 _∷_
infixr 4 _++_

mutual

  data Tel : Level → Setω where
    []   : Tel lzero
    _∷_  : (A : Set ℓ) (T : A → Tel ℓ') → Tel (ℓ ⊔ ℓ')
    _++_ : (T : Tel ℓ) (U : ⟦ T ⟧ᵗ → Tel ℓ') → Tel (ℓ ⊔ ℓ')

  ⟦_⟧ᵗ : Tel ℓ → Set ℓ
  ⟦ []     ⟧ᵗ = ⊤
  ⟦ A ∷  T ⟧ᵗ = Σ[ a ∈ A ] ⟦ T a ⟧ᵗ
  ⟦ T ++ U ⟧ᵗ = Σ[ t ∈ ⟦ T ⟧ᵗ ] ⟦ U t ⟧ᵗ

∷-syntaxᵗ : (A : Set ℓ) (T : A → Tel ℓ') → Tel (ℓ ⊔ ℓ')
∷-syntaxᵗ = _∷_

syntax ∷-syntaxᵗ A (λ x → T) = [ x ∶ A ] T

++-syntaxᵗ : (A : Tel ℓ) (T : ⟦ A ⟧ᵗ → Tel ℓ') → Tel (ℓ ⊔ ℓ')
++-syntaxᵗ = _++_

syntax ++-syntaxᵗ T (λ x → U) = [[ x ∶ T ]] U

data TelInfo (I : Set ℓ) : ∀ {ℓ'} → Tel ℓ' → Setω where
  []   : TelInfo I []
  _∷_  : {A : Set ℓ'} {T : A → Tel ℓ''}
       → I → ((a : A) → TelInfo I (T a)) → TelInfo I (A ∷ T)
  _++_ : {T : Tel ℓ'} {U : ⟦ T ⟧ᵗ → Tel ℓ''}
       → TelInfo I T → ((t : ⟦ T ⟧ᵗ) → TelInfo I (U t)) → TelInfo I (T ++ U)

constTelInfo : {I : Set ℓ} → I → {T : Tel ℓ'} → TelInfo I T
constTelInfo i {[]    } = []
constTelInfo i {A ∷  T} = i ∷ λ _ → constTelInfo i
constTelInfo i {T ++ U} = constTelInfo i ++ λ _ → constTelInfo i

Curriedᵗ : (T : Tel ℓ) → TelInfo Visibility T → (⟦ T ⟧ᵗ → Set ℓ') → Set (ℓ ⊔ ℓ')
Curriedᵗ []       _                X = X tt
Curriedᵗ (A ∷  T) (visible   ∷ vs) X = ( a : A ) → Curriedᵗ (T a) (vs a) (curry X a)
Curriedᵗ (A ∷  T) (hidden    ∷ vs) X = { a : A } → Curriedᵗ (T a) (vs a) (curry X a)
Curriedᵗ (A ∷  T) (instance′ ∷ vs) X = ⦃ a : A ⦄ → Curriedᵗ (T a) (vs a) (curry X a)
Curriedᵗ (T ++ U) (vs ++ vs')      X = Curriedᵗ  T     vs     λ t →
                                       Curriedᵗ (U t) (vs' t) λ u → X (t , u)

curryᵗ : {T : Tel ℓ} {vs : TelInfo Visibility T} {X : ⟦ T ⟧ᵗ → Set ℓ'}
       → ((t : ⟦ T ⟧ᵗ) → X t) → Curriedᵗ T vs X
curryᵗ {T = []    }                  f = f tt
curryᵗ {T = A ∷  T} {visible   ∷ vs} f = λ a → curryᵗ (curry f a)
curryᵗ {T = A ∷  T} {hidden    ∷ vs} f = curryᵗ (curry f _)
curryᵗ {T = A ∷  T} {instance′ ∷ vs} f = curryᵗ (curry f _)
curryᵗ {T = T ++ U} {vs ++ vs'}      f = curryᵗ λ t → curryᵗ λ u → f (t , u)

uncurryᵗ : {T : Tel ℓ} {vs : TelInfo Visibility T} {X : ⟦ T ⟧ᵗ → Set ℓ'}
         → Curriedᵗ T vs X → (t : ⟦ T ⟧ᵗ) → X t
uncurryᵗ {T = []    }                  f tt      = f
uncurryᵗ {T = A ∷  T} {visible   ∷ vs} f (a , t) = uncurryᵗ (f   a  ) t
uncurryᵗ {T = A ∷  T} {hidden    ∷ vs} f (a , t) = uncurryᵗ (f { a }) t
uncurryᵗ {T = A ∷  T} {instance′ ∷ vs} f (a , t) = uncurryᵗ (f ⦃ a ⦄) t
uncurryᵗ {T = T ++ U} {vs ++ vs'}      f (t , u) = uncurryᵗ (uncurryᵗ f t) u

_^_ : Set → ℕ → Set
A ^ zero  = ⊤
A ^ suc n = A × (A ^ n)
