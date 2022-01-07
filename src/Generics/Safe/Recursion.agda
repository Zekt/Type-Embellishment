{-# OPTIONS --safe --without-K #-}

module Generics.Safe.Recursion where

open import Prelude
open import Generics.Safe.Telescope
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

record FoldP : Setω where
  field
    {Desc}   : DataD
    {Native} : DataT Desc
    Conv     : DataC Desc Native
    #levels  : ℕ
  Levels : Set
  Levels = Level ^ #levels
  field
    levels   : Levels → DataD.Levels Desc
    {plevel} : Levels → Level
    Param    : ∀ ℓs → Tel (plevel ℓs)
    param    : ∀ ℓs → ⟦ Param ℓs ⟧ᵗ → ⟦ PDataD.Param (DataD.applyL Desc (levels ℓs)) ⟧ᵗ
    {clevel} : Levels → Level
    Carrier  : ∀ ℓs (ps : ⟦ Param ℓs ⟧ᵗ)
             → Carrierᶜˢ (PDataD.applyP (DataD.applyL Desc (levels ℓs)) (param ℓs ps))
                         (clevel ℓs)
    apply    : ∀ ℓs (ps : ⟦ Param ℓs ⟧ᵗ)
             → Algᶜˢ (PDataD.applyP (DataD.applyL Desc (levels ℓs)) (param ℓs ps))
                     (Carrier ℓs ps)

FoldGT : FoldP → Setω
FoldGT P = let open FoldP P in
           ∀ {ℓs} → let open PDataD (DataD.applyL Desc (levels ℓs)) in
           (ps : ⟦ FoldP.Param P ℓs ⟧ᵗ) (is : ⟦ Index (param ℓs ps) ⟧ᵗ)
         → Native (levels ℓs) (param ℓs ps) is → Carrier ℓs ps is

FoldNT : FoldP → Setω
FoldNT P = let open FoldP P in
           ∀ {ℓs} → let open PDataD (DataD.applyL Desc (levels ℓs)) in
           Curriedᵗ (FoldP.Param P ℓs) λ ps → Curriedᵗ (Index (param ℓs ps)) λ is
         → Native (levels ℓs) (param ℓs ps) is → Carrier ℓs ps is

fold-wrapper : (P : FoldP) → FoldGT P → FoldNT P
fold-wrapper P f = curryᵗ _ _ (λ ps → curryᵗ _ _ λ is → f ps is)

fold-base : (P : FoldP) → FoldNT P → FoldNT P
fold-base P rec {ℓs} = let open FoldP P in
  curryᵗ _ _ λ ps → curryᵗ _ _ λ is →
  apply ℓs ps {is} ∘ fmapᵈ Desc (λ {is} → uncurryᵗ _ _ (uncurryᵗ _ _ rec ps) is) ∘ DataC.fromN Conv

-- AlgebraC : ∀ {D N} (C : DataC D N) {ℓs ps ℓ}
--            (alg : Algebraᵈ D ℓs ps ℓ) → FoldT C alg → Set _
-- AlgebraC {D} {N} C alg fold =
--   ∀ {is} (ns : ⟦ D ⟧ᵈ (N _ _) is)
--   → fold (DataC.toN C ns) ≡ Algebra.apply alg (fmapᵈ D fold ns)

-- AlgebrasC : ∀ {D N} (C : DataC D N) {ℓf} (alg : Algebras D ℓf) → FoldsT C alg → Setω
-- AlgebrasC C alg fold = ∀ {ℓs ps} → AlgebraC C (alg ℓs ps) fold

-- AlgebrasCᵗ : ∀ {D N} (C : DataC D N) {ℓf} (alg : Algebrasᵗ D ℓf) → FoldsTᵗ C alg → Setω
-- AlgebrasCᵗ C alg fold = ∀ {ℓs ps} → AlgebraC C (alg $$ ℓs $$ ps) (fold $$ ℓs $$ ps)

-- record IndAlgebra
--   {I : Set ℓⁱ} (D : ConDs I cbs) {X : Carrierᶜˢ D ℓˣ} (f : Algᶜˢ D X) (ℓ : Level) :
--   Set (ℓⁱ ⊔ ℓˣ ⊔ lsuc ℓ ⊔ maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔
--        maxMap (hasRec? ℓˣ) cbs ⊔ maxMap (hasRec? ℓ) cbs ⊔ hasCon? ℓⁱ cbs) where
--   constructor ind-algebra
--   field
--     Carrier : IndCarrierᶜˢ D X ℓ
--     apply   : IndAlgᶜˢ D f Carrier lzero

-- record IndP : Setω where
--   field
--     {Desc}   : DataD
--     {Native} : DataT Desc
--     Conv     : DataC Desc Native
--     #levels  : ℕ
--   Levels : Set
--   Levels = Level ^ #levels
--   field
--     levels   : Levels → DataD.Levels Desc
--     {plevel} : Levels → Level
--     Param    : ∀ ℓs → Tel (plevel ℓs)
--     param    : ∀ ℓs → ⟦ Param ℓs ⟧ᵗ → ⟦ PDataD.Param (DataD.applyL Desc (levels ℓs)) ⟧ᵗ
--     {clevel} : Levels → Level
--     Carrier  : ∀ ℓs (ps : ⟦ Param ℓs ⟧ᵗ)
--              → IndCarrierᶜˢ (PDataD.applyP (DataD.applyL Desc (levels ℓs)) (param ℓs ps))
--                             (Native (levels ℓs) (param ℓs ps)) (clevel ℓs)
--     apply    : ∀ ℓs (ps : ⟦ Param ℓs ⟧ᵗ)
--              → IndAlgᶜˢ (PDataD.applyP (DataD.applyL Desc (levels ℓs)) (param ℓs ps))
--                         (DataC.toN Conv) (Carrier ℓs ps) lzero

-- IndAlgebraᵖᵈ : ∀ (D : PDataD) ps {X : Carrierᵖᵈ D ps ℓˣ} (f : Algᵖᵈ D X) ℓ → Set _
-- IndAlgebraᵖᵈ D ps f = IndAlgebra (PDataD.applyP D ps) f

-- IndAlgebraᵈ : ∀ {D N} (C : DataC D N) ℓs ps ℓ → Set _
-- IndAlgebraᵈ {D} C ℓs ps = IndAlgebraᵖᵈ (DataD.applyL D ℓs) ps (DataC.toN C)

-- IndAlgebras : ∀ {D N} (C : DataC D N) → (DataD.Levels D → Level) → Setω
-- IndAlgebras C ℓf = ∀ ℓs ps → IndAlgebraᵈ C ℓs ps (ℓf ℓs)

-- IndAlgebrasᵗ : ∀ {D N} (C : DataC D N) → (DataD.Levels D → Level) → Setω
-- IndAlgebrasᵗ C ℓf = ∀ℓ _ λ ℓs → ∀ᵗ false _ λ ps → IndAlgebraᵈ C ℓs ps (ℓf ℓs)

-- IndT : ∀ {D N} (C : DataC D N) {ℓs ps ℓ} (alg : IndAlgebraᵈ C ℓs ps ℓ) → Set _
-- IndT C alg = ∀ {is} n → IndAlgebra.Carrier alg is n

-- IndsT : ∀ {D N} (C : DataC D N) {ℓf} → IndAlgebras C ℓf → Setω
-- IndsT C alg = ∀ {ℓs ps} → IndT C (alg ℓs ps)

-- IndsTᵗ : ∀ {D N} (C : DataC D N) {ℓf} → IndAlgebrasᵗ C ℓf → Setω
-- IndsTᵗ C alg = ∀ℓ _ λ ℓs → ∀ᵗ false _ λ ps → IndT C (alg $$ ℓs $$ ps)

-- ind-base : ∀ {D N} (C : DataC D N) {ℓs ps ℓ} (alg : IndAlgebraᵈ C ℓs ps ℓ)
--          → IndT C alg → IndT C alg
-- ind-base {D} C alg rec n = subst (IndAlgebra.Carrier alg _) (DataC.toN-fromN C n)
--                              (IndAlgebra.apply alg _ (ind-fmapᵈ D rec (DataC.fromN C n)))

-- IndAlgebraC : ∀ {D N} (C : DataC D N) {ℓs ps ℓ}
--               (alg : IndAlgebraᵈ C ℓs ps ℓ) → IndT C alg → Set _
-- IndAlgebraC {D} {N} C alg ind =
--   ∀ {is} (ns : ⟦ D ⟧ᵈ (N _ _) is)
--   → ind (DataC.toN C ns) ≡ IndAlgebra.apply alg _ (ind-fmapᵈ D ind ns)

-- IndAlgebrasC : ∀ {D N} (C : DataC D N) {ℓf}
--                (alg : IndAlgebras C ℓf) → IndsT C alg → Setω
-- IndAlgebrasC C alg ind = ∀ {ℓs ps} → IndAlgebraC C (alg ℓs ps) ind

-- IndAlgebrasCᵗ : ∀ {D N} (C : DataC D N) {ℓf}
--                 (alg : IndAlgebrasᵗ C ℓf) → IndsTᵗ C alg → Setω
-- IndAlgebrasCᵗ C alg ind = ∀ {ℓs ps} → IndAlgebraC C (alg $$ ℓs $$ ps) (ind $$ ℓs $$ ps)
