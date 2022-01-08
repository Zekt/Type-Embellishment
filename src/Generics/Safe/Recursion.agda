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

FoldNT : FoldP → Setω
FoldNT P = let open FoldP P in
         ∀ {ℓs} → let open PDataD (DataD.applyL Desc (level ℓs)) in
           Curriedᵗ true (FoldP.Param P ℓs) λ ps → Curriedᵗ false (Index (param ps)) λ is
         → Native (level ℓs) (param ps) is → Carrier ℓs ps is

fold-wrapper : (P : FoldP) → FoldNT P → FoldGT P
fold-wrapper P f ps {is} n = uncurryᵗ (uncurryᵗ f ps) is n

fold-base : (P : FoldP) → FoldGT P → FoldNT P
fold-base P rec = let open FoldP P in curryᵗ λ ps → curryᵗ λ is →
  algebra ps {is} ∘ fmapᵈ Desc (rec ps) ∘ DataC.fromN Conv

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

IndNT : IndP → Setω
IndNT P = let open IndP P in
        ∀ {ℓs} → let open PDataD (DataD.applyL Desc (level ℓs)) in
          Curriedᵗ true (IndP.Param P ℓs) λ ps → Curriedᵗ false (Index (param ps)) λ is
        → (n : Native (level ℓs) (param ps) is) → Carrier ℓs ps is n

ind-wrapper : (P : IndP) → IndNT P → IndGT P
ind-wrapper P f ps {is} n = uncurryᵗ (uncurryᵗ f ps) is n

ind-base : (P : IndP) → IndGT P → IndNT P
ind-base P rec {ℓs} = let open IndP P in curryᵗ λ ps → curryᵗ λ is n →
  subst (Carrier ℓs ps is) (DataC.toN-fromN Conv n)
        (algebra ps _ (ind-fmapᵈ Desc (rec ps) (DataC.fromN Conv n)))

record IndC (P : IndP) (f : IndGT P) : Setω where
  field
    equation : let open IndP P in
             ∀ {ℓs ps is} (ns : ⟦ Desc ⟧ᵈ (Native (level ℓs) (param ps)) is)
             → f ps (DataC.toN Conv ns) ≡ algebra ps _ (ind-fmapᵈ Desc (f ps) ns)
