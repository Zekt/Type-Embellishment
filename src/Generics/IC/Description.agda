{-# OPTIONS --safe #-}

module Generics.IC.Description where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

open import Generics.Prelude

mutual

  data Tel {ℓᵇ} (B : Set ℓᵇ) ℓ : Set (lsuc (ℓᵇ ⊔ ℓ)) where
    nil  : Tel B ℓ
    snoc : (T : Tel B ℓ) (A : (b : B) → ⟦ T ⟧ᵗ b → Set ℓ) → Tel B ℓ

  ⟦_⟧ᵗ : ∀ {ℓᵇ ℓ} {B : Set ℓᵇ} → Tel B ℓ → B → Set ℓ
  ⟦ nil      ⟧ᵗ _ = Unit
  ⟦ snoc T A ⟧ᵗ b = Σ (⟦ T ⟧ᵗ b) (A b)

Tel₀ : ∀ ℓ → Set (lsuc ℓ)
Tel₀ = Tel (Unit {lzero})

⟦_⟧ᵗ⁰ : ∀ {ℓ} → Tel₀ ℓ → Set ℓ
⟦ T ⟧ᵗ⁰ = ⟦ T ⟧ᵗ tt

mutual

  weakenᵗ : ∀ {ℓᵇ ℓ} {B B' : Set ℓᵇ} → (B' → B) → Tel B ℓ → Tel B' ℓ
  weakenᵗ f  nil       = nil
  weakenᵗ f (snoc T A) = snoc (weakenᵗ f T) (λ b' wt → A (f b') (weakenᵗ-proj wt))

  weakenᵗ-proj : ∀ {ℓᵇ ℓ} {B B' : Set ℓᵇ} {f : B' → B} {T : Tel B ℓ} {b' : B'}
               → ⟦ weakenᵗ f T ⟧ᵗ b' → ⟦ T ⟧ᵗ (f b')
  weakenᵗ-proj {T = nil     } _        = tt
  weakenᵗ-proj {T = snoc T A} (wt , a) = weakenᵗ-proj wt , a

Curriedᵗ : ∀ {ℓᵇ ℓ} {B : Set ℓᵇ} (T : Tel B ℓ) (b : B) → (⟦ T ⟧ᵗ b → Set ℓ) → Set ℓ
Curriedᵗ  nil       b X = X tt
Curriedᵗ (snoc T A) b X = Curriedᵗ T b λ t → (a : A b t) → X (t , a)

curryᵗ : ∀ {ℓᵇ ℓ} {B : Set ℓᵇ} {T : Tel B ℓ} {b : B} {X : ⟦ T ⟧ᵗ b → Set ℓ}
       → ((t : ⟦ T ⟧ᵗ b) → X t) → Curriedᵗ T b X
curryᵗ {T = nil     } f = f tt
curryᵗ {T = snoc T A} f = curryᵗ (curry f)

uncurryᵗ : ∀ {ℓᵇ ℓ} {B : Set ℓᵇ} {T : Tel B ℓ} {b : B} {X : ⟦ T ⟧ᵗ b → Set ℓ}
         → Curriedᵗ T b X → (t : ⟦ T ⟧ᵗ b) → X t
uncurryᵗ {T = nil     } x _       = x
uncurryᵗ {T = snoc T A} f (t , a) = uncurryᵗ f t a

uncurryᵗ-curryᵗ : ∀ {ℓᵇ ℓ} {B : Set ℓᵇ} {T : Tel B ℓ} {b : B} {X : ⟦ T ⟧ᵗ b → Set ℓ}
                → (f : (t : ⟦ T ⟧ᵗ b) → X t) (t : ⟦ T ⟧ᵗ b) → uncurryᵗ (curryᵗ f) t ≡ f t
uncurryᵗ-curryᵗ {T = nil     } f _       = refl
uncurryᵗ-curryᵗ {T = snoc T A} f (t , a) = cong (λ g → g a) (uncurryᵗ-curryᵗ (curry f) t)

module _ {ℓᵖ ℓⁱ} (P : Tel₀ ℓᵖ) (I : Tel ⟦ P ⟧ᵗ⁰ ℓⁱ) where

  private variable T : Tel ⟦ P ⟧ᵗ⁰ ℓⁱ

  data ConD : Tel ⟦ P ⟧ᵗ⁰ ℓⁱ → Set (lsuc (ℓᵖ ⊔ ℓⁱ)) where
    ι : (i : (p : ⟦ P ⟧ᵗ⁰) (t : ⟦ T ⟧ᵗ p) → ⟦ I ⟧ᵗ p) → ConD T
    ρ : (U : Tel (Σ ⟦ P ⟧ᵗ⁰ ⟦ T ⟧ᵗ) ℓⁱ)
        (i : (p : ⟦ P ⟧ᵗ⁰) (t : ⟦ T ⟧ᵗ p) (u : ⟦ U ⟧ᵗ (p , t)) → ⟦ I ⟧ᵗ p)
        (C : ConD T) → ConD T
    σ : (A : (p : ⟦ P ⟧ᵗ⁰) (t : ⟦ T ⟧ᵗ p) → Set ℓⁱ) (C : ConD (snoc T A)) → ConD T

  data SetD : Set (lsuc (ℓᵖ ⊔ ℓⁱ)) where
    nil  : SetD
    cons : (C : ConD nil) (Cs : SetD) → SetD

module _ {ℓᵖ ℓⁱ} {P : Tel₀ ℓᵖ} {I : Tel ⟦ P ⟧ᵗ⁰ ℓⁱ} where

  ⟦_⟧ᶜ : ∀ {T} → ConD P I T → (p : ⟦ P ⟧ᵗ⁰) (t : ⟦ T ⟧ᵗ p)
       → (⟦ I ⟧ᵗ p → Set ℓⁱ) → (⟦ I ⟧ᵗ p → Set ℓⁱ)
  ⟦ ι   i   ⟧ᶜ p t X j = i p t ≡ j
  ⟦ ρ U i C ⟧ᶜ p t X j = Σ ((u : ⟦ U ⟧ᵗ (p , t)) → X (i p t u)) λ _ → ⟦ C ⟧ᶜ p t X j
  ⟦ σ A   C ⟧ᶜ p t X j = Σ (A p t) λ a → ⟦ C ⟧ᶜ p (t , a) X j

  ⟦_⟧ˢ : SetD P I → (p : ⟦ P ⟧ᵗ⁰) → (⟦ I ⟧ᵗ p → Set ℓⁱ) → (⟦ I ⟧ᵗ p → Set ℓⁱ)
  ⟦ nil       ⟧ˢ p X i = Empty
  ⟦ cons C Cs ⟧ˢ p X i = Sum (⟦ C ⟧ᶜ p tt X i) (⟦ Cs ⟧ˢ p X i)

  module _ (p : ⟦ P ⟧ᵗ⁰) (X Y : ⟦ I ⟧ᵗ p → Set ℓⁱ)
           (f : {i : ⟦ I ⟧ᵗ p} → X i → Y i) where

    fmapᶜ : ∀ {T} (C : ConD P I T) (t : ⟦ T ⟧ᵗ p)
          → {i : ⟦ I ⟧ᵗ p} → ⟦ C ⟧ᶜ p t X i → ⟦ C ⟧ᶜ p t Y i
    fmapᶜ (ι   i  ) t eq       = eq
    fmapᶜ (ρ U i C) t (x , xs) = (λ u → f (x u)) , fmapᶜ C t xs
    fmapᶜ (σ A   C) t (a , xs) = a , fmapᶜ C (t , a) xs

    fmapˢ : (D : SetD P I) → {i : ⟦ I ⟧ᵗ p} → ⟦ D ⟧ˢ p X i → ⟦ D ⟧ˢ p Y i
    fmapˢ (cons C Cs) (inl xs) = inl (fmapᶜ C tt xs)
    fmapˢ (cons C Cs) (inr xs) = inr (fmapˢ Cs   xs)