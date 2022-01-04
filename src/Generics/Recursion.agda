{-# OPTIONS --without-K #-}
open import Prelude

module Generics.Recursion where

open import Generics.Telescope; open ∀ℓ; open ∀ᵐᵗ
open import Generics.Levels
open import Generics.Description
open import Generics.Algebra

private variable
  rb  : RecB
  cb  : ConB
  cbs : ConBs

PDataT : (Dᵖ : PDataD) → Set _
PDataT Dᵖ = ∀ ps → Carrierᵖᵈ Dᵖ ps (PDataD.dlevel Dᵖ)

DataT : DataD → Setω
DataT D = ∀ ℓs → PDataT (DataD.applyL D ℓs)


{-# NO_UNIVERSE_CHECK #-}
record DataC (D : DataD) (N : DataT D) : Set where
  constructor dataC
  field
    toN   : ∀ {ℓs ps} → Algᵈ   D (N ℓs ps)
    fromN : ∀ {ℓs ps} → Coalgᵈ D (N ℓs ps)
    fromN-toN : ∀ {ℓs ps is} (ns : ⟦ D ⟧ᵈ (N ℓs ps) is) → fromN (toN ns) ≡ ns
    toN-fromN : ∀ {ℓs ps is}          (n : N ℓs ps  is) → toN (fromN n ) ≡ n
    
FoldT : ∀ {D N} (_ : DataC D N) ℓs ps (alg : Algebraᵈ D ℓs ps ℓ) → Set _
FoldT {N = N} _ ℓs ps alg = ∀ {is} → N ℓs ps is → Algebra.Carrier alg is

fold-base : ∀ {D N} (C : DataC D N) ℓs ps (alg : Algebraᵈ D ℓs ps ℓ)
          → FoldT C ℓs ps alg → FoldT C ℓs ps alg
fold-base {D = D} C ℓs ps alg rec = Algebra.apply alg ∘ fmapᵈ D rec ∘ DataC.fromN C

AlgC : ∀ {D N} (C : DataC D N) {ℓs ps ℓ} (alg : Algebraᵈ D ℓs ps ℓ) → FoldT C ℓs ps alg → Set _
AlgC {D} {N} C {ℓs} {ps} alg fold =
  ∀ {is} (ns : ⟦ D ⟧ᵈ (N ℓs ps) is)
  → Algebra.apply alg (fmapᵈ D fold ns) ≡ fold (DataC.toN C ns)

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

IndAlgC : ∀ {D N} (C : DataC D N) {ℓs ps ℓ}
          (alg : IndAlgebraᵈ C ℓs ps ℓ) → IndT C alg → Set _
IndAlgC {D} {N} C {ℓs} {ps} alg ind =
  ∀ {is} (ns : ⟦ D ⟧ᵈ (N ℓs ps) is)
  → IndAlgebra.apply alg _ (ind-fmapᵈ D ind ns) ≡ ind (DataC.toN C ns)

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

-- Curried form of `DataT` 
PDataTᶜ : (Dᵖ : PDataD) → Set _
PDataTᶜ Dᵖ = Curriedᵐᵗ true Param      λ ps →
             Curriedᵐᵗ true (Index ps) λ is →
             Set dlevel
  where open PDataD Dᵖ

DataTᶜ : DataD → Setω
DataTᶜ D = ∀ {ℓs} → PDataTᶜ (DataD.applyL D ℓs)

uncurryᵖᵈᵗ : {Dᵖ : PDataD} → PDataTᶜ Dᵖ → PDataT Dᵖ
uncurryᵖᵈᵗ {Dᵖ} N ps = uncurryᵐᵗ (Index ps) _ (uncurryᵐᵗ Param _ N ps)
  where open PDataD Dᵖ

uncurryᵈᵗ : (D : DataD) → DataTᶜ D → DataT D
uncurryᵈᵗ D N ℓs = uncurryᵖᵈᵗ {DataD.applyL D ℓs} (N {ℓs})
--
DataCᶜ : (D : DataD) (Nᶜ : DataTᶜ D) → Set
DataCᶜ D Nᶜ = DataC D (uncurryᵈᵗ D Nᶜ)