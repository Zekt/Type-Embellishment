{-# OPTIONS --safe #-}

module Generics.Safe.Ornament.Promotion where

open import Prelude
open import Generics.Safe.Telescope; open ∀ℓ; open ∀ᵐᵗ
open import Generics.Safe.Description
open import Generics.Safe.Algebra
open import Generics.Safe.Ornament
open import Generics.Safe.Ornament.Description
open import Generics.Safe.Ornament.Algebraic
open import Generics.Safe.Recursion

private variable
  rb  : RecB
  cb  : ConB
  cbs : ConBs

forget-alg : ∀ {D E N} (O : DataO D E) → DataC E N
           → ∀ℓ _ λ ℓs → ∀ᵐᵗ false _ λ ps → Algebraᵈ D ℓs ps _
forget-alg {N = N} O C $$ ℓs $$ ps = record
  { Carrier = λ is → let Oᵖ = DataO.applyL O ℓs
                     in  N (DataO.level  O  ℓs   )
                           (PDataO.param Oᵖ ps   )
                           (PDataO.index Oᵖ ps is)
  ; apply = DataC.toN C ∘ eraseᵈ O }

rememberʳ :
    {I : Set ℓⁱ} (D : RecD I rb) {N : I → Set ℓ} {X : I → Set ℓˣ}
    (g : ∀ {i} → N i → X i) {Y : ∀ i → X i × ⊤ → Set ℓʸ}
  → (ns : ⟦ D ⟧ʳ N) → Allʳ D (λ i' n → Y i' (g n , tt)) ns
  → ⟦ ⌊ algODʳ D (fmapʳ D g ns) ⌋ʳ ⟧ʳ (uncurry Y)
rememberʳ (ι i  ) g ns y   = y
rememberʳ (π A D) g ns all = λ a → rememberʳ (D a) g (ns a) (all a)

rememberᶜ :
    {I : Set ℓⁱ} (D : ConD I cb) {N : I → Set ℓ} (toN : Algᶜ D N)
    {X : I → Set ℓˣ} (f : Algᶜ D X) (g : ∀ {i} → N i → X i)
  → (∀ {i} (ns : ⟦ D ⟧ᶜ N i) → f (fmapᶜ D g ns) ≡ g (toN ns))
  → {Y : ∀ i → X i × ⊤ → Set ℓʸ}
    (toY : ∀ {i x} → ⟦ ⌊ algODᶜ D f ⌋ᶜ ⟧ᶜ (uncurry Y) (i , x , tt) → Y i (x , tt))
  → ∀ {i} (ns : ⟦ D ⟧ᶜ N i)
  → Allᶜ D (λ i' n → Y i' (g n , tt)) ns ℓ' → Y i (g (toN ns) , tt)
rememberᶜ (ι i) toN f g geq {Y} toY refl _ =
  subst (λ x → Y i (x , tt)) (geq refl) (toY refl)
rememberᶜ (σ A D) toN f g geq toY (a , ns) all =
  rememberᶜ (D a) (curry toN a) (curry f a) g (curry geq a) (curry toY a) ns all
rememberᶜ (ρ D E) toN f g geq toY (ns , ns') (all , all') =
  rememberᶜ E (curry toN ns) (curry f (fmapʳ D g ns)) g (curry geq ns)
    (curry (curry toY (fmapʳ D g ns)) (rememberʳ D g ns all)) ns' all'

rememberᶜˢ :
    {I : Set ℓⁱ} (D : ConDs I cbs) {N : I → Set ℓ} (toN : Algᶜˢ D N)
    {X : I → Set ℓˣ} (f : Algᶜˢ D X) (g : ∀ {i} → N i → X i)
  → (∀ {i} (ns : ⟦ D ⟧ᶜˢ N i) → f (fmapᶜˢ D g ns) ≡ g (toN ns))
  → {Y : ∀ i → X i × ⊤ → Set ℓʸ}
    (toY : ∀ {i x} → ⟦ ⌊ algODᶜˢ D f ⌋ᶜˢ ⟧ᶜˢ (uncurry Y) (i , x , tt) → Y i (x , tt))
  → ∀ {i} (ns : ⟦ D ⟧ᶜˢ N i)
  → Allᶜˢ D (λ i' n → Y i' (g n , tt)) ns ℓ' → Y i (g (toN ns) , tt)
rememberᶜˢ (D ∷ Ds) toN f g geq toY (inl ns) all =
  rememberᶜ  D  (toN ∘ inl) (f ∘ inl) g (geq ∘ inl) (toY ∘ inl) ns all
rememberᶜˢ (D ∷ Ds) toN f g geq toY (inr ns) all =
  rememberᶜˢ Ds (toN ∘ inr) (f ∘ inr) g (geq ∘ inr) (toY ∘ inr) ns all

remember-alg :
  ∀ {D N} (C : DataC D N) {ℓf : DataD.Levels D → Level}
    (alg : ∀ ℓs ps → Algebraᵈ D ℓs ps (ℓf ℓs)) (fold : ∀ ℓs ps → FoldT C (alg ℓs ps))
  → (∀ ℓs ps → AlgC C (alg ℓs ps) (fold ℓs ps))
  → ∀ {N'} (C' : DataC ⌊ algOD D alg ⌋ᵈ N')
  → ∀ℓ _ λ ℓs → ∀ᵐᵗ false _ λ ps → IndAlgebraᵈ C ℓs ps _
remember-alg {D} {N} C {_} alg fold algC {N'} C' $$ ℓs $$ ps = record
  { Carrier = λ is n → N' ℓs ps (is , fold ℓs ps n , tt)
  ; apply = let Dᶜˢ = PDataD.applyP (DataD.applyL D ℓs) ps
            in  rememberᶜˢ Dᶜˢ (DataC.toN C)
                  (Algebra.apply (alg ℓs ps)) (fold ℓs ps) (algC ℓs ps) (DataC.toN C') }
