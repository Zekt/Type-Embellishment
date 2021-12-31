{-# OPTIONS --safe #-}

module Generics.Safe.InductiveEquality where

open import Prelude
open import Prelude.Sum as Sum
open import Generics.Safe.Telescope; open ∀ℓ; open ∀ᵐᵗ
open import Generics.Safe.Description
open import Generics.Safe.Algebra
open import Generics.Safe.Ornament.Description
open import Generics.Safe.Ornament.Algebraic
open import Generics.Safe.Recursion

private variable
  rb  : RecB
  cb  : ConB
  cbs : ConBs

copy-algᶜ : {I : Set ℓⁱ} {D : ConD I cb} {N : Carrierᶜ D ℓ} (f : Algᶜ D N)
          → Algᶜ D (λ i → N i × N i × ⊤)
copy-algᶜ {D = D} f nns = f (fmapᶜ D fst nns) , f (fmapᶜ D (fst ∘ snd) nns) , tt

copy-algᶜˢ : {I : Set ℓⁱ} {D : ConDs I cbs} {N : Carrierᶜˢ D ℓ} (f : Algᶜˢ D N)
           → Algᶜˢ D (λ i → N i × N i × ⊤)
copy-algᶜˢ {D = D} f nns = f (fmapᶜˢ D fst nns) , f (fmapᶜˢ D (fst ∘ snd) nns) , tt

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
      ; Index  = λ ps → PDataD.Index Dᵖ ps ++ λ is →
                       (N ℓs ps is ∷ λ _ → N ℓs ps is ∷ λ _ → []) ++ λ _ → []
      ; index  = λ _  → fst
      ; applyP = λ ps → algODᶜˢ (PDataD.applyP Dᵖ ps) (copy-algᶜˢ (DataC.toN C)) } }

nonrec-from-IEq-algᶜ :
    {I : Set ℓⁱ} (D : ConD I cb) → All Sum.[ const ⊤ , (_≡ []) ] cb
  → {N : Carrierᶜ D ℓ} (f : Algᶜ D N)
  → Algᶜ ⌊ algODᶜ D (copy-algᶜ f) ⌋ᶜ (λ i → let (_ , (n , n' , _) , _) = i in n ≡ n')
nonrec-from-IEq-algᶜ (ι i  ) nr f refl = refl
nonrec-from-IEq-algᶜ (σ A D) (_ ∷ nr) f (a , es) =
  nonrec-from-IEq-algᶜ (D a) nr (curry f a) es
nonrec-from-IEq-algᶜ (ρ (ι i) D) (refl ∷ nr) f ((n , .n , _) , refl , es) =
  nonrec-from-IEq-algᶜ D nr (curry f n) es

nonrec-from-IEq-algᶜˢ :
    {I : Set ℓⁱ} (D : ConDs I cbs) → All (All Sum.[ const ⊤ , (_≡ []) ]) cbs
  → {N : Carrierᶜˢ D ℓ} (f : Algᶜˢ D N)
  → Algᶜˢ ⌊ algODᶜˢ D (copy-algᶜˢ f) ⌋ᶜˢ (λ i → let (_ , (n , n' , _) , _) = i in n ≡ n')
nonrec-from-IEq-algᶜˢ (D ∷ Ds) (nr ∷ _) f (inl es) =
  nonrec-from-IEq-algᶜ  D  nr (f ∘ inl) es
nonrec-from-IEq-algᶜˢ (D ∷ Ds) (_ ∷ nr) f (inr es) =
  nonrec-from-IEq-algᶜˢ Ds nr (f ∘ inr) es

nonrec-from-IEq-alg :
  ∀ {D N} (C : DataC D N)
  → (∀ ℓs → All (All Sum.[ const ⊤ , (_≡ []) ]) (PDataD.struct (DataD.applyL D ℓs)))
  → ∀ℓ _ λ ℓs → ∀ᵐᵗ false _ λ ps → Algebraᵈ ⌊ IEqOD C ⌋ᵈ ℓs ps _
nonrec-from-IEq-alg {D} C nr $$ ℓs $$ ps = record
  { Carrier = λ i → let (_ , (n , n' , _) , _) = i in n ≡ n'
  ; apply = let Dᶜˢ = (PDataD.applyP (DataD.applyL D ℓs) ps)
            in  nonrec-from-IEq-algᶜˢ Dᶜˢ (nr ℓs) (DataC.toN C) }

FunExt : Setω
FunExt = ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (a : A) → B a}
       → (∀ a → f a ≡ g a) → f ≡ g

from-IEq-algʳ :
    FunExt → {I : Set ℓⁱ} (D : RecD I rb) {N : I → Set ℓ}
    (ns : ⟦ D ⟧ʳ (λ i → N i × N i × ⊤))
    (es : ⟦ ⌊ algODʳ D ns ⌋ʳ ⟧ʳ (λ i → let (_ , (n , n' , _) , _) = i in n ≡ n'))
  → fmapʳ D fst ns ≡ fmapʳ D (fst ∘ snd) ns
from-IEq-algʳ funext (ι i) ns eq = eq
from-IEq-algʳ funext (π A D) ns es = funext λ a → from-IEq-algʳ funext (D a) (ns a) (es a)

from-IEq-algᶜ :
    FunExt → {I : Set ℓⁱ} (D : ConD I cb)
    {N : Carrierᶜ D ℓ} (f : Algᶜ D N)
  → Algᶜ ⌊ algODᶜ D (copy-algᶜ f) ⌋ᶜ (λ i → let (_ , (n , n' , _) , _) = i in n ≡ n')
from-IEq-algᶜ funext (ι i  ) f refl = refl
from-IEq-algᶜ funext (σ A D) f (a , es) = from-IEq-algᶜ funext (D a) (curry f a) es
from-IEq-algᶜ funext (ρ D E) f (nns , es , es') =
  from-IEq-algᶜ funext E (curry f (fmapʳ D (fst ∘ snd) nns))
    (subst (λ ns' → ⟦ ⌊ algODᶜ E (λ nns' → f (ns'            , fmapᶜ E fst nns')
                                         , f (fmapʳ D (fst ∘ snd) nns
                                            , fmapᶜ E (fst ∘ snd) nns')
                                         , tt) ⌋ᶜ ⟧ᶜ
                      (λ i → let (_ , (n , n' , _) , _) = i in n ≡ n') _)
           (from-IEq-algʳ funext D nns es) es')

from-IEq-algᶜˢ :
    FunExt → {I : Set ℓⁱ} (D : ConDs I cbs)
    {N : Carrierᶜˢ D ℓ} (f : Algᶜˢ D N)
  → Algᶜˢ ⌊ algODᶜˢ D (copy-algᶜˢ f) ⌋ᶜˢ (λ i → let (_ , (n , n' , _) , _) = i in n ≡ n')
from-IEq-algᶜˢ funext (D ∷ Ds) f (inl es) = from-IEq-algᶜ  funext D  (f ∘ inl) es
from-IEq-algᶜˢ funext (D ∷ Ds) f (inr es) = from-IEq-algᶜˢ funext Ds (f ∘ inr) es

from-IEq-alg : ∀ {D N} (C : DataC D N) → FunExt
             → ∀ℓ _ λ ℓs → ∀ᵐᵗ false _ λ ps → Algebraᵈ ⌊ IEqOD C ⌋ᵈ ℓs ps _
from-IEq-alg {D} C funext $$ ℓs $$ ps = record
  { Carrier = λ i → let (_ , (n , n' , _) , _) = i in n ≡ n'
  ; apply = let Dᶜˢ = (PDataD.applyP (DataD.applyL D ℓs) ps)
            in  from-IEq-algᶜˢ funext Dᶜˢ (DataC.toN C) }
