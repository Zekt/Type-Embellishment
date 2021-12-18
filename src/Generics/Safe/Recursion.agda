{-# OPTIONS --safe #-}

module Generics.Safe.Recursion where

open import Prelude
open import Generics.Safe.Telescope
open import Generics.Safe.Description
open import Generics.Safe.Algebra
open import Generics.Safe.Ornament.Description
open Generics.Safe.Ornament.Description.ODFunctor
open import Generics.Safe.Ornament.Algebraic

private variable
  rb  : RecB
  cb  : ConB
  cbs : ConBs

DataT : DataD → Setω
DataT D = Carrierᵈ D (λ ℓs → PDataD.dlevel (DataD.applyL D ℓs))

record DataC (D : DataD) (N : DataT D) : Setω where
  field
    toN   : Algᵈ   D N
    fromN : Coalgᵈ D N
    fromN-toN : ∀ {ℓs ps is} (ns : ⟦ D ⟧ᵈ (N ℓs ps) is) → fromN (toN ns) ≡ ns
    toN-fromN : ∀ {ℓs ps is}          (n : N ℓs ps  is) → toN (fromN n ) ≡ n

FoldT : ∀ {D N} (_ : DataC D N) ℓs ps (alg : Algebraᵈ D ℓs ps ℓ) → Set _
FoldT {N = N} _ ℓs ps alg = ∀ {is} → N ℓs ps is → Algebra.Carrier alg is

fold-base : ∀ {D N} (C : DataC D N) ℓs ps (alg : Algebraᵈ D ℓs ps ℓ)
          → FoldT C ℓs ps alg → FoldT C ℓs ps alg
fold-base {D = D} C ℓs ps alg rec = Algebra.apply alg ∘ fmapᵈ D rec ∘ DataC.fromN C

AlgC : ∀ {D N} (C : DataC D N) ℓs ps (alg : Algebraᵈ D ℓs ps ℓ) → FoldT C ℓs ps alg → Set _
AlgC {N = N} C ℓs ps alg fold =
  ∀ {is} (n : N ℓs ps is) → fold-base C ℓs ps alg fold n ≡ fold n

ind-fmapʳ : {I : Set ℓⁱ} (D : RecD I rb) {X : I → Set ℓ}
            {P : Σ I X → Set ℓ'} → (∀ {i} x → P (i , x))
          → (xs : ⟦ D ⟧ʳ X) → ⟦ ⌊ algODʳ D X xs ⌋ʳ ⟧ʳ P
ind-fmapʳ (ι i  ) Pt x  = Pt x
ind-fmapʳ (π A D) Pt xs = λ a → ind-fmapʳ (D a) Pt (xs a)

ind-fmapᶜ : {I : Set ℓⁱ} (D : ConD I cb) {X : Carrierᶜ D ℓ} (f : Algᶜ D X)
            {P : Σ I X → Set ℓ'} → (∀ {i} x → P (i , x))
          → ∀ {i} (xs : ⟦ D ⟧ᶜ X i) → ⟦ ⌊ algODᶜ D X f ⌋ᶜ ⟧ᶜ P (i , f xs)
ind-fmapᶜ (ι i  ) f Pt refl       = refl
ind-fmapᶜ (σ A D) f Pt (a , xs)   = a , ind-fmapᶜ (D a) (curry f a) Pt xs
ind-fmapᶜ (ρ D E) f Pt (xs , xs') = xs , ind-fmapʳ D Pt xs ,
                                    ind-fmapᶜ E (curry f xs) Pt xs'

ind-fmapᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) {X : Carrierᶜˢ D ℓ} (f : Algᶜˢ D X)
             {P : Σ I X → Set ℓ'} → (∀ {i} x → P (i , x))
           → ∀ {i} (xs : ⟦ D ⟧ᶜˢ X i) → ⟦ ⌊ algODᶜˢ D X f ⌋ᶜˢ ⟧ᶜˢ P (i , f xs)
ind-fmapᶜˢ (D ∷ Ds) f Pt (inl xs) = inl (ind-fmapᶜ  D  (f ∘ inl) Pt xs)
ind-fmapᶜˢ (D ∷ Ds) f Pt (inr xs) = inr (ind-fmapᶜˢ Ds (f ∘ inr) Pt xs)

IndFmapTᵖᵈ : (D : PDataD) → (∀ ps → Algebraᵖᵈ D ps ℓ) → (ℓ' : Level) → Set _
IndFmapTᵖᵈ D alg ℓ' = ∀ {ps} → let X = Algebra.Carrier (alg ps) in
                      {P : ⟦ snocᵗ (PDataD.Index D ps) X ⟧ᵗ → Set ℓ'}
                    → (∀ {i} x → P (snocᵗ-inj (i , x)))
                    → ∀ {i x} (xs : ⟦ D ⟧ᵖᵈ X i) → Algebra.apply (alg ps) xs ≡ x
                    → ⟦ ⌊ algODᵖᵈ D alg ⌋ᵖᵈ ⟧ᵖᵈ P (snocᵗ-inj (i , x))

ind-fmapᵖᵈ : (D : PDataD) (alg : ∀ ps → Algebraᵖᵈ D ps ℓ) → IndFmapTᵖᵈ D alg ℓ'
ind-fmapᵖᵈ D alg {ps} Pt xs refl =
  imapOD-injᶜˢ (algODᶜˢ (PDataD.applyP D ps) _ (Algebra.apply (alg ps)))
               (ind-fmapᶜˢ (PDataD.applyP D ps) (Algebra.apply (alg ps)) Pt xs)

ind-fmapᵈ : (D : DataD) {ℓf : DataD.Levels D → Level} (alg : ∀ ℓs ps → Algebraᵈ D ℓs ps (ℓf ℓs))
          → ∀ {ℓs ℓ} → IndFmapTᵖᵈ (DataD.applyL D ℓs) (alg ℓs) ℓ
ind-fmapᵈ D alg {ℓs} = ind-fmapᵖᵈ (DataD.applyL D ℓs) (alg ℓs)

ind-fmap : ∀ {D N} (C : DataC D N) {ℓs ℓ}
         → IndFmapTᵖᵈ (DataD.applyL D ℓs) (λ ps → algebra _ (DataC.toN C)) ℓ
ind-fmap {D} C = ind-fmapᵈ D (λ ℓs ps → algebra _ (DataC.toN C))

IndAlg : ∀ {D N} (_ : DataC D N) ℓs ps ℓ → Set _
IndAlg {D} {N} C ℓs ps ℓ = Algebraᵈ ⌊ algODᵈ D (λ _ _ → algebra _ (DataC.toN C)) ⌋ᵈ ℓs ps ℓ

IndT : ∀ {D N} (C : DataC D N) {ℓs ps ℓ} (alg : IndAlg C ℓs ps ℓ) → Set _
IndT {D} {N} C {ℓs} {ps} alg = ∀ {is} (n : N ℓs ps is)
                             → Algebra.Carrier alg (snocᵗ-inj (is , n))

ind-base : ∀ {D N} (C : DataC D N) {ℓs ps} (alg : IndAlg C ℓs ps ℓ) → IndT C alg → IndT C alg
ind-base C alg rec n =
  Algebra.apply alg (ind-fmap C rec (DataC.fromN C n) (DataC.toN-fromN C n))

IndAlgC : ∀ {D N} (C : DataC D N) {ℓs ps ℓ} (alg : IndAlg C ℓs ps ℓ) → IndT C alg → Set _
IndAlgC {N = N} C alg ind = ∀ {is} (n : N _ _ is) → ind-base C alg ind n ≡ ind n
