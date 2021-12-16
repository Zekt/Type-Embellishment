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
DataT D = Carrierᵈ D (λ ℓs → let Dᵖ = DataD.applyL D ℓs
                             in  PDataD.dlevel Dᵖ ⊔ PDataD.ilevel Dᵖ)

record DataC (D : DataD) (N : DataT D) : Setω where
  field
    toN   : Algᵈ   D N
    fromN : Coalgᵈ D N
    fromN-toN : ∀ {ℓs ps is} (ns : ⟦ D ⟧ᵈ (N ℓs ps) is) → fromN (toN ns) ≡ ns
    toN-fromN : ∀ {ℓs ps is}          (n : N ℓs ps  is) → toN (fromN n ) ≡ n

FoldT : ∀ {D N} (_ : DataC D N) {ℓs ps} (alg : Algebraᵈ D ℓs ps ℓ) → Set _
FoldT {N = N} _ {ℓs} {ps} alg = ∀ {is} → N ℓs ps is → Algebraᵖᵈ.Carrier alg is

fold-base : ∀ {D N} (C : DataC D N) {ℓs ps} (alg : Algebraᵈ D ℓs ps ℓ)
          → FoldT C alg → FoldT C alg
fold-base {D = D} C alg rec = Algebraᵖᵈ.apply alg ∘ fmapᵈ D rec ∘ DataC.fromN C

AlgC : ∀ {D N} (C : DataC D N) {ℓs ps} (alg : Algebraᵈ D ℓs ps ℓ) → FoldT C alg → Set _
AlgC {N = N} C {ℓs} {ps} alg fold =
  ∀ {is} (n : N ℓs ps is) → fold-base C alg fold n ≡ fold n

-- ind-fmapʳ : {I : Set ℓⁱ} (D : RecD I rb) {X : I → Set ℓ}
--             {P : Σ I X → Set ℓ'} → (∀ {i} x → P (i , x))
--           → (xs : ⟦ D ⟧ʳ X) → ⟦ ⌊ algODʳ D X xs ⌋ʳ ⟧ʳ P
-- ind-fmapʳ (ι i  ) Pt x  = Pt x
-- ind-fmapʳ (π A D) Pt xs = λ a → ind-fmapʳ (D a) Pt (xs a)

-- ind-fmapᶜ : {I : Set ℓⁱ} (D : ConD I cb) {X : Carrierᶜ D ℓ} (f : Algᶜ D X)
--             {P : Σ I X → Set ℓ'} → (∀ {i} x → P (i , x))
--           → ∀ {i} (xs : ⟦ D ⟧ᶜ X i) → ⟦ ⌊ algODᶜ D X f ⌋ᶜ ⟧ᶜ P (i , f xs)
-- ind-fmapᶜ (ι i  ) f Pt refl       = refl
-- ind-fmapᶜ (σ A D) f Pt (a , xs)   = a , ind-fmapᶜ (D a) (curry f a) Pt xs
-- ind-fmapᶜ (ρ D E) f Pt (xs , xs') = xs , ind-fmapʳ D Pt xs ,
--                                     ind-fmapᶜ E (curry f xs) Pt xs'

-- ind-fmapᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) {X : Carrierᶜˢ D ℓ} (f : Algᶜˢ D X)
--              {P : Σ I X → Set ℓ'} → (∀ {i} x → P (i , x))
--            → ∀ {i} (xs : ⟦ D ⟧ᶜˢ X i) → ⟦ ⌊ algODᶜˢ D X f ⌋ᶜˢ ⟧ᶜˢ P (i , f xs)
-- ind-fmapᶜˢ (D ∷ Ds) f Pt (inl xs) = inl (ind-fmapᶜ  D  (f ∘ inl) Pt xs)
-- ind-fmapᶜˢ (D ∷ Ds) f Pt (inr xs) = inr (ind-fmapᶜˢ Ds (f ∘ inr) Pt xs)

-- IndFmapTᵖᵈ : (D : PDataD) {X : Carrierᵖᵈ D ℓ} (f : Algᵖᵈ D X) → Setω
-- IndFmapTᵖᵈ D {X} f = ∀ {ps ℓ'} {P : ⟦ snocᵗ (PDataD.Index D ps) (X ps) ⟧ᵗ → Set ℓ'}
--                    → (∀ {i} x → P (snocᵗ-inj (i , x)))
--                    → ∀ {i x} (xs : ⟦ D ⟧ᵖᵈ (X ps) i) → f xs ≡ x
--                    → ⟦ ⌊ algODᵖᵈ D X f ⌋ᵖᵈ ⟧ᵖᵈ P (snocᵗ-inj (i , x))

-- ind-fmapᵖᵈ : (D : PDataD) {X : Carrierᵖᵈ D ℓ} (f : Algᵖᵈ D X) → IndFmapTᵖᵈ D f
-- ind-fmapᵖᵈ D f {ps} Pt xs refl =
--   imapOD-injᶜˢ (algODᶜˢ (PDataD.applyP D ps) _ f) (ind-fmapᶜˢ (PDataD.applyP D ps) f Pt xs)

-- ind-fmapᵈ : (D : DataD) {ℓf : DataD.Levels D → Level} {X : Carrierᵈ D ℓf} (f : Algᵈ D X)
--           → ∀ {ℓs} → IndFmapTᵖᵈ (DataD.applyL D ℓs) f
-- ind-fmapᵈ D f {ℓs} = ind-fmapᵖᵈ (DataD.applyL D ℓs) f

-- IndAlg : ∀ {D N} → DataC D N → Setω
-- IndAlg {D} {N} C = Alg ⌊ algODᵈ D N (DataC.toN C) ⌋ᵈ

-- IndRT : ∀ {D N} (C : DataC D N) (alg : IndAlg C)
--       → ∀ ℓs → ⟦ PDataD.Param (DataD.applyL D ℓs) ⟧ᵗ → Set _
-- IndRT {D} {N} C alg ℓs ps =
--   ∀ {is} (n : N ℓs ps is) → Alg.Carrier alg ℓs ps (snocᵗ-inj (is , n))

-- IndT : ∀ {D N} (C : DataC D N) → IndAlg C → Setω
-- IndT C alg = ∀ {ℓs ps} → IndRT C alg ℓs ps

-- ind-base : ∀ {D N} (C : DataC D N) (alg : IndAlg C)
--          → ∀ {ℓs ps} → IndRT C alg ℓs ps → IndRT C alg ℓs ps
-- ind-base {D} C alg rec n =
--   Alg.apply alg (ind-fmapᵈ D (DataC.toN C) rec (DataC.fromN C n) (DataC.toN-fromN C n))

-- IndAlgC : ∀ {D N} (C : DataC D N) (alg : IndAlg C) → IndT C alg → Setω
-- IndAlgC {N = N} C alg ind = ∀ {ℓs ps is} (n : N ℓs ps is) → ind-base C alg ind n ≡ ind n
