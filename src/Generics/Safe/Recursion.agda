{-# OPTIONS --safe --without-K #-}

module Generics.Safe.Recursion where

open import Prelude
open import Generics.Safe.Telescope; open ∀ℓ; open ∀ᵐᵗ
open import Generics.Safe.Description
open import Generics.Safe.Algebra

private variable
  rb  : RecB
  cb  : ConB
  cbs : ConBs

DataT : DataD → Setω
DataT D = Carriers D (λ ℓs → PDataD.dlevel (DataD.applyL D ℓs))

record DataC (D : DataD) (N : DataT D) : Setω where
  field
    toN   : Algs   D N
    fromN : Coalgs D N
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

Algebras : (D : DataD) → (DataD.Levels D → Level) → Setω
Algebras D ℓf = ∀ ℓs ps → Algebraᵈ D ℓs ps (ℓf ℓs)

Algebrasᵗ : (D : DataD) → (DataD.Levels D → Level) → Setω
Algebrasᵗ D ℓf = ∀ℓ _ λ ℓs → ∀ᵐᵗ false _ λ ps → Algebraᵈ D ℓs ps (ℓf ℓs)

FoldT : ∀ {D N} (_ : DataC D N) {ℓs ps ℓ} (alg : Algebraᵈ D ℓs ps ℓ) → Set _
FoldT {D} {N} _ alg = ∀ {is} → N _ _ is → Algebra.Carrier alg is

FoldsT : ∀ {D N} (_ : DataC D N) {ℓf} → Algebras D ℓf → Setω
FoldsT C alg = ∀ {ℓs ps} → FoldT C (alg ℓs ps)

FoldsTᵗ : ∀ {D N} (_ : DataC D N) {ℓf} → Algebrasᵗ D ℓf → Setω
FoldsTᵗ C alg = ∀ℓ _ λ ℓs → ∀ᵐᵗ false _ λ ps → FoldT C (alg $$ ℓs $$ ps)

fold-base : ∀ {D N} (C : DataC D N) {ℓs ps} (alg : Algebraᵈ D ℓs ps ℓ)
          → FoldT C alg → FoldT C alg
fold-base {D = D} C alg rec = Algebra.apply alg ∘ fmapᵈ D rec ∘ DataC.fromN C

AlgebraC : ∀ {D N} (C : DataC D N) {ℓs ps ℓ}
           (alg : Algebraᵈ D ℓs ps ℓ) → FoldT C alg → Set _
AlgebraC {D} {N} C alg fold =
  ∀ {is} (ns : ⟦ D ⟧ᵈ (N _ _) is)
  → fold (DataC.toN C ns) ≡ Algebra.apply alg (fmapᵈ D fold ns)

AlgebrasC : ∀ {D N} (C : DataC D N) {ℓf} (alg : Algebras D ℓf) → FoldsT C alg → Setω
AlgebrasC C alg fold = ∀ {ℓs ps} → AlgebraC C (alg ℓs ps) fold

AlgebrasCᵗ : ∀ {D N} (C : DataC D N) {ℓf} (alg : Algebrasᵗ D ℓf) → FoldsTᵗ C alg → Setω
AlgebrasCᵗ C alg fold = ∀ {ℓs ps} → AlgebraC C (alg $$ ℓs $$ ps) (fold $$ ℓs $$ ps)

record IndAlgebra
  {I : Set ℓⁱ} (D : ConDs I cbs) {X : Carrierᶜˢ D ℓˣ} (f : Algᶜˢ D X) (ℓ : Level) :
  Set (ℓⁱ ⊔ ℓˣ ⊔ lsuc ℓ ⊔ maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔
       maxMap (hasRec? ℓˣ) cbs ⊔ maxMap (hasRec? ℓ) cbs ⊔ hasCon? ℓⁱ cbs) where
  constructor ind-algebra
  field
    Carrier : IndCarrierᶜˢ D X ℓ
    apply   : IndAlgᶜˢ D f Carrier lzero

IndAlgebraᵖᵈ : ∀ (D : PDataD) ps {X : Carrierᵖᵈ D ps ℓˣ} (f : Algᵖᵈ D X) ℓ → Set _
IndAlgebraᵖᵈ D ps f = IndAlgebra (PDataD.applyP D ps) f

IndAlgebraᵈ : ∀ {D N} (C : DataC D N) ℓs ps ℓ → Set _
IndAlgebraᵈ {D} C ℓs ps = IndAlgebraᵖᵈ (DataD.applyL D ℓs) ps (DataC.toN C)

IndAlgebras : ∀ {D N} (C : DataC D N) → (DataD.Levels D → Level) → Setω
IndAlgebras C ℓf = ∀ ℓs ps → IndAlgebraᵈ C ℓs ps (ℓf ℓs)

IndAlgebrasᵗ : ∀ {D N} (C : DataC D N) → (DataD.Levels D → Level) → Setω
IndAlgebrasᵗ C ℓf = ∀ℓ _ λ ℓs → ∀ᵐᵗ false _ λ ps → IndAlgebraᵈ C ℓs ps (ℓf ℓs)

IndT : ∀ {D N} (C : DataC D N) {ℓs ps ℓ} (alg : IndAlgebraᵈ C ℓs ps ℓ) → Set _
IndT C alg = ∀ {is} n → IndAlgebra.Carrier alg is n

IndsT : ∀ {D N} (C : DataC D N) {ℓf} → IndAlgebras C ℓf → Setω
IndsT C alg = ∀ {ℓs ps} → IndT C (alg ℓs ps)

IndsTᵗ : ∀ {D N} (C : DataC D N) {ℓf} → IndAlgebrasᵗ C ℓf → Setω
IndsTᵗ C alg = ∀ℓ _ λ ℓs → ∀ᵐᵗ false _ λ ps → IndT C (alg $$ ℓs $$ ps)

ind-base : ∀ {D N} (C : DataC D N) {ℓs ps ℓ} (alg : IndAlgebraᵈ C ℓs ps ℓ)
         → IndT C alg → IndT C alg
ind-base {D} C alg rec n = subst (IndAlgebra.Carrier alg _) (DataC.toN-fromN C n)
                             (IndAlgebra.apply alg _ (ind-fmapᵈ D rec (DataC.fromN C n)))

IndAlgebraC : ∀ {D N} (C : DataC D N) {ℓs ps ℓ}
              (alg : IndAlgebraᵈ C ℓs ps ℓ) → IndT C alg → Set _
IndAlgebraC {D} {N} C alg ind =
  ∀ {is} (ns : ⟦ D ⟧ᵈ (N _ _) is)
  → ind (DataC.toN C ns) ≡ IndAlgebra.apply alg _ (ind-fmapᵈ D ind ns)

IndAlgebrasC : ∀ {D N} (C : DataC D N) {ℓf}
               (alg : IndAlgebras C ℓf) → IndsT C alg → Setω
IndAlgebrasC C alg ind = ∀ {ℓs ps} → IndAlgebraC C (alg ℓs ps) ind

IndAlgebrasCᵗ : ∀ {D N} (C : DataC D N) {ℓf}
                (alg : IndAlgebrasᵗ C ℓf) → IndsTᵗ C alg → Setω
IndAlgebrasCᵗ C alg ind = ∀ {ℓs ps} → IndAlgebraC C (alg $$ ℓs $$ ps) (ind $$ ℓs $$ ps)
