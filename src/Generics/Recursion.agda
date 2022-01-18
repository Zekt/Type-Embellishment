{-# OPTIONS --safe --without-K #-}

open import Prelude

module Generics.Recursion where
open import Generics.Telescope
open import Generics.Description
open import Generics.Algebra

private variable
  rb  : RecB
  cb  : ConB
  cbs : ConBs

DataT : DataD → Setω
DataT D = Carriers D (λ ℓs → PDataD.dlevel (DataD.applyL D ℓs))

record DataC (D : DataD) (N : DataT D) : Setω where
  constructor datac
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
    level    : Levels → DataD.Levels Desc
    {plevel} : Levels → Level
    Param    : ∀ ℓs → Tel (plevel ℓs)
    param    : ∀ {ℓs} → ⟦ Param ℓs ⟧ᵗ → ⟦ PDataD.Param (DataD.applyL Desc (level ℓs)) ⟧ᵗ
    {clevel} : Levels → Level
    Carrier  : ∀ ℓs (ps : ⟦ Param ℓs ⟧ᵗ)
             → Carrierᶜˢ (PDataD.applyP (DataD.applyL Desc (level ℓs)) (param ps))
                         (clevel ℓs)
    algebra  : ∀ {ℓs} (ps : ⟦ Param ℓs ⟧ᵗ)
             → Algᶜˢ (PDataD.applyP (DataD.applyL Desc (level ℓs)) (param ps))
                     (Carrier ℓs ps)

FoldGT : FoldP → Setω
FoldGT P = let open FoldP P in
         ∀ {ℓs} → let open PDataD (DataD.applyL Desc (level ℓs)) in
           (ps : ⟦ FoldP.Param P ℓs ⟧ᵗ) {is : ⟦ Index (param ps) ⟧ᵗ}
         → Native (level ℓs) (param ps) is → Carrier ℓs ps is

FoldNT : (P : FoldP)   → let open FoldP P in
         (ℓs : Levels) → let open PDataD (DataD.applyL Desc (level ℓs)) hiding (plevel) in
         Set (alevel ⊔ ilevel ⊔ FoldP.plevel P ℓs ⊔ clevel ℓs)
FoldNT P ℓs = Curriedᵗ true (FoldP.Param P ℓs) λ ps → Curriedᵗ false (Index (param ps)) λ is
         → Native (level ℓs) (param ps) is → Carrier ℓs ps is
  where open FoldP P
        open PDataD (DataD.applyL Desc (level ℓs))

fold-wrapper : (P : FoldP) → (∀ {ℓs} → FoldNT P ℓs) → FoldGT P
fold-wrapper P f ps {is} = uncurryᵗ (uncurryᵗ f ps) is

fold-base : (P : FoldP) → ∀ {ℓs} → FoldNT P ℓs → FoldNT P ℓs
fold-base P {ℓs} rec = let open FoldP P in
  curryᵗ λ ps → curryᵗ λ is →
    algebra ps {is}
  ∘ fmapᵈ Desc (λ {is} → uncurryᵗ (uncurryᵗ rec ps) is)
  ∘ DataC.fromN Conv

record FoldC (P : FoldP) (f : FoldGT P) : Setω where
  field
    equation : let open FoldP P in
             ∀ {ℓs ps is} (ns : ⟦ Desc ⟧ᵈ (Native (level ℓs) (param ps)) is)
             → f ps (DataC.toN Conv ns) ≡ algebra ps (fmapᵈ Desc (f ps) ns)

record IndP : Setω where
  field
    {Desc}   : DataD
    {Native} : DataT Desc
    Conv     : DataC Desc Native
    #levels  : ℕ
  Levels : Set
  Levels = Level ^ #levels
  field
    level    : Levels → DataD.Levels Desc
    {plevel} : Levels → Level
    Param    : ∀ ℓs → Tel (plevel ℓs)
    param    : ∀ {ℓs} → ⟦ Param ℓs ⟧ᵗ → ⟦ PDataD.Param (DataD.applyL Desc (level ℓs)) ⟧ᵗ
    {clevel} : Levels → Level
    Carrier  : ∀ ℓs (ps : ⟦ Param ℓs ⟧ᵗ)
             → IndCarrierᶜˢ (PDataD.applyP (DataD.applyL Desc (level ℓs)) (param ps))
                            (Native (level ℓs) (param ps)) (clevel ℓs)
    algebra  : ∀ {ℓs} (ps : ⟦ Param ℓs ⟧ᵗ)
             → IndAlgᶜˢ (PDataD.applyP (DataD.applyL Desc (level ℓs)) (param ps))
                        (DataC.toN Conv) (Carrier ℓs ps) lzero

IndGT : IndP → Setω
IndGT P = let open IndP P in
        ∀ {ℓs} → let open PDataD (DataD.applyL Desc (level ℓs)) in
          (ps : ⟦ IndP.Param P ℓs ⟧ᵗ) {is : ⟦ Index (param ps) ⟧ᵗ}
        → (n : Native (level ℓs) (param ps) is) → Carrier ℓs ps is n

IndNT : (P : IndP)    → let open IndP P in
        (ℓs : Levels) → let open PDataD (DataD.applyL Desc (level ℓs)) hiding (plevel) in
        Set (alevel ⊔ ilevel ⊔ plevel ℓs ⊔ clevel ℓs)
IndNT P ℓs = Curriedᵗ true  (IndP.Param P ℓs)  λ ps →
             Curriedᵗ false (Index (param ps)) λ is →
             (n : Native (level ℓs) (param ps) is)
           → Carrier ℓs ps is n
        where open IndP P
              open PDataD (DataD.applyL Desc (level ℓs))

ind-wrapper : (P : IndP) → (∀ {ℓs} → IndNT P ℓs) → IndGT P
ind-wrapper P f ps {is} = uncurryᵗ (uncurryᵗ f ps) is

ind-base : (P : IndP) → (∀ {ℓs} → IndNT P ℓs → IndNT P ℓs)
ind-base P {ℓs} rec = let open IndP P in
  curryᵗ λ ps → curryᵗ λ is n →
  subst (Carrier ℓs ps is) (DataC.toN-fromN Conv n)
        (algebra ps _ (ind-fmapᵈ Desc
                                 (λ {is} →
                                    uncurryᵗ (uncurryᵗ rec ps) is)
                                 (DataC.fromN Conv n)))

record IndC (P : IndP) (f : IndGT P) : Setω where
  field
    equation : let open IndP P in
             ∀ {ℓs ps is} (ns : ⟦ Desc ⟧ᵈ (Native (level ℓs) (param ps)) is)
             → f ps (DataC.toN Conv ns) ≡ algebra ps _ (ind-fmapᵈ Desc (f ps) ns)

-- Curried form of `DataT`
PDataTᶜ : (Dᵖ : PDataD) → Set _
PDataTᶜ Dᵖ = Curriedᵗ true Param      λ ps →
             Curriedᵗ true (Index ps) λ is →
             Set dlevel
  where open PDataD Dᵖ

DataTᶜ : DataD → Setω
DataTᶜ D = ∀ {ℓs} → PDataTᶜ (DataD.applyL D ℓs)

uncurryᵈᵗ : (D : DataD) → DataTᶜ D → DataT D
uncurryᵈᵗ D N ℓs ps = uncurryᵗ (uncurryᵗ N ps)

DataCᶜ : (D : DataD) (Nᶜ : DataTᶜ D) → Setω
DataCᶜ D Nᶜ = DataC D (uncurryᵈᵗ D Nᶜ)
