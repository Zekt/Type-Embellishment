{-# OPTIONS --safe #-}

module Generics.Safe.Ornament.Algebraic.Properties where

open import Prelude
open import Generics.Safe.Telescope; open ∀ℓ; open ∀ᵗ
open import Generics.Safe.Description
open import Generics.Safe.Algebra
open import Generics.Safe.Ornament
open import Generics.Safe.Ornament.Description
open Generics.Safe.Ornament.Description.ODFunctor
open import Generics.Safe.Ornament.Algebraic
open import Generics.Safe.Recursion

private variable
  rb  : RecB
  cb  : ConB
  cbs : ConBs

inhabitanceʳ :
    {I : Set ℓⁱ} (D : RecD I rb) {N : I → Set ℓ} {X : I → Set ℓˣ}
    (g : ∀ {i} → N i → X i) {Y : ∀ i → X i → Set ℓʸ}
  → (ns : ⟦ D ⟧ʳ N) → Allʳ D (λ i' n → Y i' (g n)) ns
  → ⟦ ⌊ algODʳ D (fmapʳ D g ns) ⌋ʳ ⟧ʳ (uncurry Y)
inhabitanceʳ (ι i  ) g ns y   = y
inhabitanceʳ (π A D) g ns all = λ a → inhabitanceʳ (D a) g (ns a) (all a)

inhabitanceᶜ :
    {I : Set ℓⁱ} (D : ConD I cb) {N : I → Set ℓ} (toN : Algᶜ D N)
    {X : I → Set ℓˣ} (f : Algᶜ D X) (g : ∀ {i} → N i → X i)
  → (∀ {i} (ns : ⟦ D ⟧ᶜ N i) → f (fmapᶜ D g ns) ≡ g (toN ns))
  → {Y : ∀ i → X i → Set ℓʸ}
    (toY : ∀ {i x} → ⟦ ⌊ algODᶜ D f ⌋ᶜ ⟧ᶜ (uncurry Y) (i , x) → Y i x)
  → ∀ {i} (ns : ⟦ D ⟧ᶜ N i) → Allᶜ D (λ i' n → Y i' (g n)) ns ℓ' → Y i (g (toN ns))
inhabitanceᶜ (ι i  ) toN f g geq {Y} toY refl _ =
  subst (Y i) (geq refl) (toY refl)
inhabitanceᶜ (σ A D) toN f g geq toY (a , ns) all =
  inhabitanceᶜ (D a) (curry toN a) (curry f a) g (curry geq a) (curry toY a) ns all
inhabitanceᶜ (ρ D E) toN f g geq toY (ns , ns') (all , all') =
  inhabitanceᶜ E (curry toN ns) (curry f (fmapʳ D g ns)) g (curry geq ns)
    (curry (curry toY (fmapʳ D g ns)) (inhabitanceʳ D g ns all)) ns' all'

inhabitanceᶜˢ :
    {I : Set ℓⁱ} (D : ConDs I cbs) {N : I → Set ℓ} (toN : Algᶜˢ D N)
    {X : I → Set ℓˣ} (f : Algᶜˢ D X) (g : ∀ {i} → N i → X i)
  → (∀ {i} (ns : ⟦ D ⟧ᶜˢ N i) → f (fmapᶜˢ D g ns) ≡ g (toN ns))
  → {Y : ∀ i → X i → Set ℓʸ}
    (toY : ∀ {i x} → ⟦ ⌊ algODᶜˢ D f ⌋ᶜˢ ⟧ᶜˢ (uncurry Y) (i , x) → Y i x)
  → ∀ {i} (ns : ⟦ D ⟧ᶜˢ N i) → Allᶜˢ D (λ i' n → Y i' (g n)) ns ℓ' → Y i (g (toN ns))
inhabitanceᶜˢ (D ∷ Ds) toN f g geq toY (inl ns) all =
  inhabitanceᶜ  D  (toN ∘ inl) (f ∘ inl) g (geq ∘ inl) (toY ∘ inl) ns all
inhabitanceᶜˢ (D ∷ Ds) toN f g geq toY (inr ns) all =
  inhabitanceᶜˢ Ds (toN ∘ inr) (f ∘ inr) g (geq ∘ inr) (toY ∘ inr) ns all

inhabitance :
  ∀ {D N} (C : DataC D N) {ℓf : DataD.Levels D → Level}
    (alg : ∀ ℓs ps → Algebraᵈ D ℓs ps (ℓf ℓs))
    (fold : ∀ ℓs ps → FoldT C (alg ℓs ps))
  → (∀ ℓs ps → AlgC C (alg ℓs ps) (fold ℓs ps))
  → ∀ {N'} (C' : DataC ⌊ algODᵈ D alg ⌋ᵈ N')
  → ∀ℓ _ λ ℓs → ∀ᵗ false _ λ ps → IndAlgebraᵈ C ℓs ps _
inhabitance {D} {N} C alg fold algC {N'} C' $$ ℓs $$ ps = record
  { Carrier = λ is n → N' ℓs ps (snocᵗ-inj (is , fold ℓs ps n))
  ; apply = let Dᶜˢ = PDataD.applyP (DataD.applyL D ℓs) ps
            in inhabitanceᶜˢ Dᶜˢ (DataC.toN C)
                 (Algebra.apply (alg ℓs ps)) (fold ℓs ps) (algC ℓs ps)
                 (DataC.toN C' ∘ imapOD-injᶜˢ (algODᶜˢ Dᶜˢ (Algebra.apply (alg ℓs ps)))) }
