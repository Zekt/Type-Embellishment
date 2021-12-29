{-# OPTIONS --safe #-}

module Generics.Safe.InductiveEquality where

open import Prelude
open import Prelude.Sum as Sum
open import Generics.Safe.Telescope; open ∀ℓ; open ∀ᵗ
open import Generics.Safe.Description
open import Generics.Safe.Algebra
open import Generics.Safe.Ornament.Description
open Generics.Safe.Ornament.Description.ODFunctor
open import Generics.Safe.Ornament.Algebraic
open import Generics.Safe.Recursion

private variable
  rb  : RecB
  cb  : ConB
  cbs : ConBs

copy-algᶜ : {I : Set ℓⁱ} {D : ConD I cb} {N : Carrierᶜ D ℓ} (f : Algᶜ D N)
          → Algᶜ D (λ i → N i × N i)
copy-algᶜ {D = D} f nns = f (fmapᶜ D fst nns) , f (fmapᶜ D snd nns)

copy-algᶜˢ : {I : Set ℓⁱ} {D : ConDs I cbs} {N : Carrierᶜˢ D ℓ} (f : Algᶜˢ D N)
           → Algᶜˢ D (λ i → N i × N i)
copy-algᶜˢ {D = D} f nns = f (fmapᶜˢ D fst nns) , f (fmapᶜˢ D snd nns)

IEqOD : ∀ {D N} → DataC D N → DataOD D
IEqOD {D} {N} C = record
  { #levels = DataD.#levels D
  ; level   = id
  ; applyL  = λ ℓs → let Dᵖ = DataD.applyL D ℓs in record
      { alevel = PDataD.alevel Dᵖ
      ; level-pre-fixed-point =
          algOD-pfp-lemma (PDataD.dlevel Dᵖ) (PDataD.ilevel Dᵖ) (PDataD.dlevel Dᵖ)
                          (PDataD.struct Dᵖ) (PDataD.level-pre-fixed-point Dᵖ)
      ; Param  = PDataD.Param Dᵖ
      ; param  = id
      ; Index  = λ ps → snoc²ᵗ (PDataD.Index Dᵖ ps) (N ℓs ps) (N ℓs ps)
      ; index  = λ ps → fst ∘ snoc²ᵗ-proj
      ; applyP = λ ps → imapODᶜˢ snoc²ᵗ-proj snoc²ᵗ-inj snoc²ᵗ-proj-inj
                          (algODᶜˢ (PDataD.applyP Dᵖ ps) (copy-algᶜˢ (DataC.toN C))) } }

nonrec-from-IEq-algᶜ :
    {I : Set ℓⁱ} (D : ConD I cb) → All Sum.[ const ⊤ , (_≡ []) ] cb
  → {N : Carrierᶜ D ℓ} (f : Algᶜ D N)
  → Algᶜ ⌊ algODᶜ D (copy-algᶜ f) ⌋ᶜ (uncurry _≡_ ∘ snd)
nonrec-from-IEq-algᶜ (ι i  ) nr f refl = refl
nonrec-from-IEq-algᶜ (σ A D) (_ ∷ nr) f (a , es) =
  nonrec-from-IEq-algᶜ (D a) nr (curry f a) es
nonrec-from-IEq-algᶜ (ρ (ι i) D) (refl ∷ nr) f ((n , .n) , refl , es) =
  nonrec-from-IEq-algᶜ D nr (curry f n) es

nonrec-from-IEq-algᶜˢ :
    {I : Set ℓⁱ} (D : ConDs I cbs) → All (All Sum.[ const ⊤ , (_≡ []) ]) cbs
  → {N : Carrierᶜˢ D ℓ} (f : Algᶜˢ D N)
  → Algᶜˢ ⌊ algODᶜˢ D (copy-algᶜˢ f) ⌋ᶜˢ (uncurry _≡_ ∘ snd)
nonrec-from-IEq-algᶜˢ (D ∷ Ds) (nr ∷ _) f (inl es) =
  nonrec-from-IEq-algᶜ  D  nr (f ∘ inl) es
nonrec-from-IEq-algᶜˢ (D ∷ Ds) (_ ∷ nr) f (inr es) =
  nonrec-from-IEq-algᶜˢ Ds nr (f ∘ inr) es

nonrec-from-IEq-alg :
  ∀ {D N} (C : DataC D N)
  → (∀ ℓs → All (All Sum.[ const ⊤ , (_≡ []) ]) (PDataD.struct (DataD.applyL D ℓs)))
  → ∀ℓ _ λ ℓs → ∀ᵗ false _ λ ps → Algebraᵈ ⌊ IEqOD C ⌋ᵈ ℓs ps _
nonrec-from-IEq-alg {D} C nr $$ ℓs $$ ps = record
  { Carrier = λ is → uncurry _≡_ (snd (snoc²ᵗ-proj is))
  ; apply = let Dᶜˢ = (PDataD.applyP (DataD.applyL D ℓs) ps)
            in  nonrec-from-IEq-algᶜˢ  Dᶜˢ (nr ℓs) (DataC.toN C)
              ∘ imapOD-projᶜˢ (algODᶜˢ Dᶜˢ (copy-algᶜˢ (DataC.toN C))) }

FunExt : Setω
FunExt = ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (a : A) → B a}
       → (∀ a → f a ≡ g a) → f ≡ g

from-IEq-algʳ : FunExt → {I : Set ℓⁱ} (D : RecD I rb) {N : I → Set ℓ}
                (ns : ⟦ D ⟧ʳ (λ i → N i × N i))
                (es : ⟦ ⌊ algODʳ D ns ⌋ʳ ⟧ʳ (uncurry _≡_ ∘ snd))
              → fmapʳ D fst ns ≡ fmapʳ D snd ns
from-IEq-algʳ funext (ι i) ns eq = eq
from-IEq-algʳ funext (π A D) ns es = funext λ a → from-IEq-algʳ funext (D a) (ns a) (es a)

from-IEq-algᶜ : FunExt → {I : Set ℓⁱ} (D : ConD I cb)
                {N : Carrierᶜ D ℓ} (f : Algᶜ D N)
              → Algᶜ ⌊ algODᶜ D (copy-algᶜ f) ⌋ᶜ (uncurry _≡_ ∘ snd)
from-IEq-algᶜ funext (ι i  ) f refl = refl
from-IEq-algᶜ funext (σ A D) f (a , es) = from-IEq-algᶜ funext (D a) (curry f a) es
from-IEq-algᶜ funext (ρ D E) f (ns , es , es') =
  from-IEq-algᶜ funext E (curry f (fmapʳ D snd ns))
    (subst (λ ns' → ⟦ ⌊ algODᶜ E (λ nns → f (ns'            , fmapᶜ E fst nns)
                                        , f (fmapʳ D snd ns , fmapᶜ E snd nns)) ⌋ᶜ ⟧ᶜ
                      (uncurry _≡_ ∘ snd) _)
           (from-IEq-algʳ funext D ns es) es')

from-IEq-algᶜˢ : FunExt → {I : Set ℓⁱ} (D : ConDs I cbs)
                 {N : Carrierᶜˢ D ℓ} (f : Algᶜˢ D N)
               → Algᶜˢ ⌊ algODᶜˢ D (copy-algᶜˢ f) ⌋ᶜˢ (uncurry _≡_ ∘ snd)
from-IEq-algᶜˢ funext (D ∷ Ds) f (inl es) = from-IEq-algᶜ  funext D  (f ∘ inl) es
from-IEq-algᶜˢ funext (D ∷ Ds) f (inr es) = from-IEq-algᶜˢ funext Ds (f ∘ inr) es

from-IEq-alg : ∀ {D N} (C : DataC D N) → FunExt
             → ∀ℓ _ λ ℓs → ∀ᵗ false _ λ ps → Algebraᵈ ⌊ IEqOD C ⌋ᵈ ℓs ps _
from-IEq-alg {D} C funext $$ ℓs $$ ps = record
  { Carrier = λ is → uncurry _≡_ (snd (snoc²ᵗ-proj is))
  ; apply = let Dᶜˢ = (PDataD.applyP (DataD.applyL D ℓs) ps)
            in  from-IEq-algᶜˢ funext  Dᶜˢ (DataC.toN C)
              ∘ imapOD-projᶜˢ (algODᶜˢ Dᶜˢ (copy-algᶜˢ (DataC.toN C))) }
