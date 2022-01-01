{-# OPTIONS --safe #-}

module Generics.Safe.Recursion where

open import Prelude
open import Generics.Safe.Description
open import Generics.Safe.Algebra

private variable
  rb  : RecB
  cb  : ConB
  cbs : ConBs

DataT : DataD → Setω
DataT D = ∀ ℓs ps → Carrierᵈ D ℓs ps (PDataD.dlevel (DataD.applyL D ℓs))

record DataC (D : DataD) (N : DataT D) : Setω where
  field
    toN   : ∀ {ℓs ps} → Algᵈ   D (N ℓs ps)
    fromN : ∀ {ℓs ps} → Coalgᵈ D (N ℓs ps)
    fromN-toN : ∀ {ℓs ps is} (ns : ⟦ D ⟧ᵈ (N ℓs ps) is) → fromN (toN ns) ≡ ns
    toN-fromN : ∀ {ℓs ps is}          (n : N ℓs ps  is) → toN (fromN n ) ≡ n

record Algebra {I : Set ℓⁱ} (D : ConDs I cbs) ℓ
     : Set (ℓⁱ ⊔ maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ maxMap (hasRec? ℓ) cbs ⊔
            hasCon? ℓⁱ cbs ⊔ lsuc ℓ) where
  constructor algebra
  field
    Carrier : Carrierᶜˢ D ℓ
    apply   : Algᶜˢ D Carrier

Algebraᵖᵈ : ∀ (D : PDataD) ps ℓ → Set _
Algebraᵖᵈ D ps = Algebra (PDataD.applyP D ps)

Algebraᵈ : ∀ (D : DataD) ℓs ps ℓ → Set _
Algebraᵈ D ℓs = Algebraᵖᵈ (DataD.applyL D ℓs)


FoldT : ∀ {D N} (_ : DataC D N) {ℓs ps ℓ} (alg : Algebraᵈ D ℓs ps ℓ) → Set _
FoldT {D} {N} _ alg = ∀ {is} → N _ _ is → Algebra.Carrier alg is

fold-base : ∀ {D N} (C : DataC D N) {ℓs ps} (alg : Algebraᵈ D ℓs ps ℓ)
          → FoldT C alg → FoldT C alg
fold-base {D = D} C alg rec = Algebra.apply alg ∘ fmapᵈ D rec ∘ DataC.fromN C

AlgC : ∀ {D N} (C : DataC D N) {ℓs ps ℓ} (alg : Algebraᵈ D ℓs ps ℓ) → FoldT C alg → Set _
AlgC {D} {N} C alg fold = ∀ {is} (ns : ⟦ D ⟧ᵈ (N _ _) is)
                        → fold (DataC.toN C ns) ≡ Algebra.apply alg (fmapᵈ D fold ns)

record IndAlgebra
  {I : Set ℓⁱ} (D : ConDs I cbs) {X : Carrierᶜˢ D ℓˣ} (f : Algᶜˢ D X) (ℓ : Level) :
  Set (ℓⁱ ⊔ ℓˣ ⊔ lsuc ℓ ⊔ maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔
       maxMap (hasRec? ℓˣ) cbs ⊔ maxMap (hasRec? ℓ) cbs ⊔ hasCon? ℓⁱ cbs) where
  constructor ind-algebra
  field
    Carrier : IndCarrierᶜˢ D X ℓ
    apply   : IndAlgᶜˢ D f Carrier

IndAlgebraᵖᵈ : ∀ (D : PDataD) ps {X : Carrierᵖᵈ D ps ℓˣ} (f : Algᵖᵈ D X) ℓ → Set _
IndAlgebraᵖᵈ D ps f = IndAlgebra (PDataD.applyP D ps) f

IndAlgebraᵈ : ∀ {D N} (C : DataC D N) ℓs ps ℓ → Set _
IndAlgebraᵈ {D} C ℓs ps = IndAlgebraᵖᵈ (DataD.applyL D ℓs) ps (DataC.toN C)

IndT : ∀ {D N} (C : DataC D N) {ℓs ps ℓ} (alg : IndAlgebraᵈ C ℓs ps ℓ) → Set _
IndT C alg = ∀ {is} n → IndAlgebra.Carrier alg is n

ind-base : ∀ {D N} (C : DataC D N) {ℓs ps ℓ} (alg : IndAlgebraᵈ C ℓs ps ℓ)
         → IndT C alg → IndT C alg
ind-base {D} C alg rec n = subst (IndAlgebra.Carrier alg _) (DataC.toN-fromN C n)
                             (IndAlgebra.apply alg _ (ind-fmapᵈ D rec (DataC.fromN C n)))

IndAlgC : ∀ {D N} (C : DataC D N) {ℓs ps ℓ}
          (alg : IndAlgebraᵈ C ℓs ps ℓ) → IndT C alg → Set _
IndAlgC {D} {N} C {ℓs} {ps} alg ind =
  ∀ {is} (ns : ⟦ D ⟧ᵈ (N ℓs ps) is)
  → ind (DataC.toN C ns) ≡ IndAlgebra.apply alg _ (ind-fmapᵈ D ind ns)
