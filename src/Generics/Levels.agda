{-# OPTIONS --without-K #-}

open import Prelude

module Generics.Levels where

open import Generics.Telescope

RecB : Set
RecB = List Level

ConB : Set
ConB = List (Level ⊎ RecB)

ConBs : Set
ConBs = List ConB

max-ℓ : List Level → Level
max-ℓ = foldr lzero _⊔_

maxMap : {A : Set} → (A → Level) → List A → Level
maxMap f = max-ℓ ∘ map f

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
             → (∀ a → f a ⊑ ℓ) → ∀ as → maxMap f as ⊑ ℓ
maxMap-bound f ℓ eq []       = refl
maxMap-bound f ℓ eq (a ∷ as) = cong₂ _⊔_ (eq a) (maxMap-bound f ℓ eq as)

hasRec?-bound : ∀ ℓ cb → hasRec? ℓ cb ⊑ ℓ
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
