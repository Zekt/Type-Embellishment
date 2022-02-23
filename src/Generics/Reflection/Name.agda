{-# OPTIONS --without-K --safe #-}
open import Prelude

module Generics.Reflection.Name where

open import Utils.Reflection
open import Utils.Error as Err

open import Generics.Description 
open import Generics.Recursion   
open import Generics.Reflection.Telescope

DataToNativeName : (D : DataD) (N : DataT D) → TC Name
DataToNativeName D N = do
  exCxtℓs #levels λ ℓs → let Desc = applyL ℓs in
    exCxtTel (PDataD.Param Desc) λ ps →
      exCxtTel (PDataD.Index Desc ps) λ is → do
        (def n _) ← quoteTC! (N ℓs ps is)
          where t → notData t
        return n
  where open DataD D

FoldPToNativeName : FoldP → TC Name
FoldPToNativeName P = do
  exCxtℓs (DataD.#levels Desc) λ ℓs →
    exCxtTel (PDataD.Param (DataD.applyL Desc ℓs)) λ ps → 
      exCxtTel (PDataD.Index (DataD.applyL Desc ℓs) ps) λ is → do
        (def d _) ← quoteTC! $ Native ℓs ps is
          where t → IMPOSSIBLE
        return d
  where open FoldP P

IndPToNativeName : IndP → TC Name
IndPToNativeName P = do
  exCxtℓs (DataD.#levels Desc) λ ℓs →
    exCxtTel (PDataD.Param (DataD.applyL Desc ℓs)) λ ps → 
      exCxtTel (PDataD.Index (DataD.applyL Desc ℓs) ps) λ is → do
        (def d _) ← quoteTC! $ Native ℓs ps is
          where t → IMPOSSIBLE
        return d
  where open IndP P
