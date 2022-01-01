{-# OPTIONS --safe #-}

module Generics.Safe.InductiveEquality where

open import Prelude
import Prelude.List as List
open import Prelude.Sum as Sum
open import Generics.Safe.Telescope; open ∀ℓ; open ∀ᵐᵗ
open import Generics.Safe.Description
open import Generics.Safe.Algebra
open import Generics.Safe.Recursion
open import Generics.Safe.Ornament
open import Generics.Safe.Ornament.Description

private variable
  rb  : RecB
  cb  : ConB
  cbs : ConBs

IEqODʳ : {I : Set ℓⁱ} (D : RecD I rb) {N : I → Set ℓ} (ns ns' : ⟦ D ⟧ʳ N)
       → RecOD (Σ[ i ∈ I ] N i × N i × ⊤) fst D
IEqODʳ (ι i  ) n  n'  = ι (_ , n , n' , tt) refl
IEqODʳ (π A D) ns ns' = π λ a → IEqODʳ (D a) (ns a) (ns' a)

IEqConB : Level → ConB → ConB
IEqConB ℓ []            = []
IEqConB ℓ (inl ℓ' ∷ cb) = inl ℓ' ∷ IEqConB ℓ cb
IEqConB ℓ (inr rb ∷ cb) = inl (max-ℓ rb ⊔ ℓ) ∷ inl (max-ℓ rb ⊔ ℓ) ∷ inr rb ∷ IEqConB ℓ cb

IEqODᶜ : {I : Set ℓⁱ} (D : ConD I cb) {N : I → Set ℓ}
       → Algᶜ D N → Algᶜ D N → ConOD (Σ[ i ∈ I ] N i × N i × ⊤) fst D (IEqConB ℓ cb)
IEqODᶜ (ι i  ) f f' = ι (_ , f refl , f' refl , tt) refl
IEqODᶜ (σ A D) f f' = σ λ a → IEqODᶜ (D a) (curry f a) (curry f' a)
IEqODᶜ (ρ D E) f f' = Δ (⟦ D ⟧ʳ _) λ ns → Δ (⟦ D ⟧ʳ _) λ ns' →
                      ρ (IEqODʳ D ns ns') (IEqODᶜ E (curry f ns) (curry f' ns'))

IEqODᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) {N : I → Set ℓ}
        → Algᶜˢ D N → ConODs (Σ[ i ∈ I ] N i × N i × ⊤) fst D (List.map (IEqConB ℓ) cbs)
IEqODᶜˢ []       f = []
IEqODᶜˢ (D ∷ Ds) f = IEqODᶜ D (f ∘ inl) (f ∘ inl) ∷ ∺ IEqODᶜˢ Ds (f ∘ inr)

module _ (ℓ : Level) where

  IEqConB-lemma₀ : ∀ cb → max-π (IEqConB ℓ cb) ≡ max-π cb
  IEqConB-lemma₀ []            = refl
  IEqConB-lemma₀ (inl ℓ' ∷ cb) = IEqConB-lemma₀ cb
  IEqConB-lemma₀ (inr rb ∷ cb) = cong (max-ℓ rb ⊔_) (IEqConB-lemma₀ cb)

  IEqConB-lemma₁ : ∀ cbs → maxMap max-π (List.map (IEqConB ℓ) cbs) ≡ maxMap max-π cbs
  IEqConB-lemma₁ []         = refl
  IEqConB-lemma₁ (cb ∷ cbs) = cong₂ _⊔_ (IEqConB-lemma₀ cb) (IEqConB-lemma₁ cbs)

  IEqConB-lemma₂ : ∀ cb → max-σ (IEqConB ℓ cb) ≡ max-π cb ⊔ max-σ cb ⊔ hasRec? ℓ cb
  IEqConB-lemma₂ []            = refl
  IEqConB-lemma₂ (inl ℓ' ∷ cb) = cong (ℓ' ⊔_) (IEqConB-lemma₂ cb)
  IEqConB-lemma₂ (inr rb ∷ cb) = cong (ℓ ⊔ max-ℓ rb ⊔_) (IEqConB-lemma₂ cb)

  IEqConB-lemma₃ : ∀ cbs → maxMap max-σ (List.map (IEqConB ℓ) cbs)
                          ≡ maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ maxMap (hasRec? ℓ) cbs
  IEqConB-lemma₃ []         = refl
  IEqConB-lemma₃ (cb ∷ cbs) = cong₂ _⊔_ (IEqConB-lemma₂ cb) (IEqConB-lemma₃ cbs)

  IEqOD-pfp-lemma :
      (ℓⁱ ℓᵃ : Level) (cbs : ConBs)
    → maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ maxMap (hasRec? (ℓᵃ ⊔ ℓⁱ)) cbs ⊔
      hasCon? ℓⁱ cbs ⊔ ℓᵃ ⊔ ℓⁱ ≡ ℓᵃ ⊔ ℓⁱ
    → maxMap max-π (List.map (IEqConB ℓ) cbs) ⊔
      maxMap max-σ (List.map (IEqConB ℓ) cbs) ⊔
      maxMap (hasRec? (ℓᵃ ⊔ ℓⁱ ⊔ ℓ)) (List.map (IEqConB ℓ) cbs) ⊔
      hasCon? (ℓⁱ ⊔ ℓ) (List.map (IEqConB ℓ) cbs) ⊔ ℓᵃ ⊔ ℓⁱ ⊔ ℓ ≡ ℓᵃ ⊔ ℓⁱ ⊔ ℓ
  IEqOD-pfp-lemma ℓⁱ ℓᵃ cbs pfp' =
    begin
      maxMap max-π (List.map (IEqConB ℓ) cbs) ⊔
      maxMap max-σ (List.map (IEqConB ℓ) cbs) ⊔
      maxMap (hasRec? (ℓᵃ ⊔ ℓⁱ ⊔ ℓ)) (List.map (IEqConB ℓ) cbs) ⊔
      hasCon? (ℓⁱ ⊔ ℓ) (List.map (IEqConB ℓ) cbs) ⊔ ℓᵃ ⊔ ℓⁱ ⊔ ℓ
        ≡⟨ -- eliminating IEqConB; boundedness of level-conditionals
          (let cbs' = List.map (IEqConB ℓ) cbs
            in  cong₂ _⊔_ (cong₂ _⊔_ (cong₂ _⊔_
              (IEqConB-lemma₁ cbs)
              (IEqConB-lemma₃ cbs))
              (maxMap-bound (hasRec? (ℓᵃ ⊔ ℓⁱ ⊔ ℓ)) _
                            (hasRec?-bound (ℓᵃ ⊔ ℓⁱ ⊔ ℓ)) cbs'))
              (hasCon?-bound (ℓⁱ ⊔ ℓ) cbs')) ⟩
      maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ maxMap (hasRec? ℓ) cbs ⊔ ℓᵃ ⊔ ℓ ⊔ ℓⁱ
        ≡⟨ -- boundedness of level-conditionals
            cong (maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔_) (cong₂ _⊔_ (cong₂ _⊔_
          (maxMap-bound (hasRec? ℓ) _ (hasRec?-bound ℓ) cbs)
          (sym (maxMap-bound (hasRec? (ℓᵃ ⊔ ℓⁱ)) _ (hasRec?-bound (ℓᵃ ⊔ ℓⁱ)) cbs)))
          (sym (hasCon?-bound ℓⁱ cbs))) ⟩
      maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ maxMap (hasRec? (ℓᵃ ⊔ ℓⁱ)) cbs ⊔
      hasCon? ℓⁱ cbs ⊔ ℓᵃ ⊔ ℓⁱ ⊔ ℓ
        ≡⟨ cong (ℓ ⊔_) pfp' ⟩
      ℓᵃ ⊔ ℓⁱ ⊔ ℓ
    ∎ where open ≡-Reasoning

IEqOD : ∀ {D N} → DataC D N → DataOD D
IEqOD {D} {N} C = record
  { #levels = DataD.#levels D
  ; level   = id
  ; applyL  = λ ℓs → let Dᵖ = DataD.applyL D ℓs in record
      { alevel = PDataD.alevel Dᵖ
      ; level-pre-fixed-point = IEqOD-pfp-lemma
          (PDataD.dlevel Dᵖ) (PDataD.ilevel Dᵖ) (PDataD.dlevel Dᵖ) (PDataD.struct Dᵖ)
          (PDataD.level-pre-fixed-point Dᵖ)
      ; Param  = PDataD.Param Dᵖ
      ; param  = id
      ; Index  = λ ps → PDataD.Index Dᵖ ps ++ λ is →
                        N ℓs ps is ∷ λ _ → N ℓs ps is ∷ λ _ → []
      ; index  = λ _  → fst
      ; applyP = λ ps → IEqODᶜˢ (PDataD.applyP Dᵖ ps) (DataC.toN C) } }

IEqD : ∀ {D N} → DataC D N → DataD
IEqD C = ⌊ IEqOD C ⌋ᵈ

IEq-refl-algʳ :
    {I : Set ℓⁱ} (D : RecD I rb) {N : I → Set ℓ}
    {E : Σ[ i ∈ I ] N i × N i × ⊤ → Set ℓ'}
    (ns : ⟦ D ⟧ʳ N) → Allʳ D (λ i n → E (i , n , n , tt)) ns
  → ⟦ ⌊ IEqODʳ D ns ns ⌋ʳ ⟧ʳ E
IEq-refl-algʳ (ι i  ) n  e   = e
IEq-refl-algʳ (π A D) ns all = λ a → IEq-refl-algʳ (D a) (ns a) (all a)

IEq-refl-algᶜ :
    {I : Set ℓⁱ} (D : ConD I cb) {N : I → Set ℓ} (toN : Algᶜ D N)
    {E : Σ[ i ∈ I ] N i × N i × ⊤ → Set ℓ'}
  → ∀ {i} (ns : ⟦ D ⟧ᶜ N i) → Allᶜ D (λ i n → E (i , n , n , tt)) ns ℓ''
  → ⟦ ⌊ IEqODᶜ D toN toN ⌋ᶜ ⟧ᶜ E (i , toN ns , toN ns , tt)
IEq-refl-algᶜ (ι i  ) toN refl all = refl
IEq-refl-algᶜ (σ A D) toN (a , ns) all = a , IEq-refl-algᶜ (D a) (curry toN a) ns all
IEq-refl-algᶜ (ρ D E) toN (ns , ns') (all , all') =
  ns , ns , IEq-refl-algʳ D ns all , IEq-refl-algᶜ E (curry toN ns) ns' all'

IEq-refl-algᶜˢ :
    {I : Set ℓⁱ} (D : ConDs I cbs) {N : I → Set ℓ} (toN : Algᶜˢ D N)
    {E : Σ[ i ∈ I ] N i × N i × ⊤ → Set ℓ'}
  → ∀ {i} (ns : ⟦ D ⟧ᶜˢ N i) → Allᶜˢ D (λ i n → E (i , n , n , tt)) ns ℓ''
  → ⟦ ⌊ IEqODᶜˢ D toN ⌋ᶜˢ ⟧ᶜˢ E (i , toN ns , toN ns , tt)
IEq-refl-algᶜˢ (D ∷ Ds) toN (inl ns) all = inl (IEq-refl-algᶜ  D  (toN ∘ inl) ns all)
IEq-refl-algᶜˢ (D ∷ Ds) toN (inr ns) all = inr (IEq-refl-algᶜˢ Ds (toN ∘ inr) ns all)

IEq-refl-alg : ∀ {D N} (C : DataC D N) → ∀ {E} → DataC (IEqD C) E
             → ∀ℓ _ λ ℓs → ∀ᵐᵗ false _ λ ps → IndAlgebraᵈ C ℓs ps _
IEq-refl-alg {D} C {E} EC $$ ℓs $$ ps = record
  { Carrier = λ is n → E ℓs ps (is , n , n , tt)
  ; apply = λ ns all → DataC.toN EC
      (IEq-refl-algᶜˢ (PDataD.applyP (DataD.applyL D ℓs) ps) (DataC.toN C) ns all) }

nonrec-from-IEq-algᶜ :
    {I : Set ℓⁱ} (D : ConD I cb) → All Sum.[ const ⊤ , (_≡ []) ] cb
  → {N : Carrierᶜ D ℓ} (f : Algᶜ D N)
  → Algᶜ ⌊ IEqODᶜ D f f ⌋ᶜ (λ i → let (_ , n , n' , _) = i in n ≡ n')
nonrec-from-IEq-algᶜ (ι i  ) nr f refl = refl
nonrec-from-IEq-algᶜ (σ A D) (_ ∷ nr) f (a , es) =
  nonrec-from-IEq-algᶜ (D a) nr (curry f a) es
nonrec-from-IEq-algᶜ (ρ (ι i) D) (refl ∷ nr) f (n , .n , refl , es) =
  nonrec-from-IEq-algᶜ D nr (curry f n) es

nonrec-from-IEq-algᶜˢ :
    {I : Set ℓⁱ} (D : ConDs I cbs) → All (All Sum.[ const ⊤ , (_≡ []) ]) cbs
  → {N : Carrierᶜˢ D ℓ} (f : Algᶜˢ D N)
  → Algᶜˢ ⌊ IEqODᶜˢ D f ⌋ᶜˢ (λ i → let (_ , n , n' , _) = i in n ≡ n')
nonrec-from-IEq-algᶜˢ (D ∷ Ds) (nr ∷ _) f (inl es) =
  nonrec-from-IEq-algᶜ  D  nr (f ∘ inl) es
nonrec-from-IEq-algᶜˢ (D ∷ Ds) (_ ∷ nr) f (inr es) =
  nonrec-from-IEq-algᶜˢ Ds nr (f ∘ inr) es

nonrec-from-IEq-alg :
  ∀ {D N} (C : DataC D N)
  → (∀ ℓs → All (All Sum.[ const ⊤ , (_≡ []) ]) (PDataD.struct (DataD.applyL D ℓs)))
  → ∀ℓ _ λ ℓs → ∀ᵐᵗ false _ λ ps → Algebraᵈ (IEqD C) ℓs ps _
nonrec-from-IEq-alg {D} C nr $$ ℓs $$ ps = record
  { Carrier = λ i → let (_ , n , n' , _) = i in n ≡ n'
  ; apply = let Dᶜˢ = PDataD.applyP (DataD.applyL D ℓs) ps
            in  nonrec-from-IEq-algᶜˢ Dᶜˢ (nr ℓs) (DataC.toN C) }

FunExt : Setω
FunExt = ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (a : A) → B a}
       → (∀ a → f a ≡ g a) → f ≡ g

from-IEq-algʳ :
    FunExt → {I : Set ℓⁱ} (D : RecD I rb) {N : I → Set ℓ} {ns ns' : ⟦ D ⟧ʳ N}
    (es : ⟦ ⌊ IEqODʳ D ns ns' ⌋ʳ ⟧ʳ (λ i → let (_ , n , n' , _) = i in n ≡ n'))
  → ns ≡ ns'
from-IEq-algʳ funext (ι i  ) eq = eq
from-IEq-algʳ funext (π A D) es = funext λ a → from-IEq-algʳ funext (D a) (es a)

from-IEq-algᶜ :
    FunExt → {I : Set ℓⁱ} (D : ConD I cb) {N : Carrierᶜ D ℓ}
    (f f' : Algᶜ D N) → (∀ {i} (ns : ⟦ D ⟧ᶜ N i) → f ns ≡ f' ns)
  → Algᶜ ⌊ IEqODᶜ D f f' ⌋ᶜ (λ i → let (_ , n , n' , _) = i in n ≡ n')
from-IEq-algᶜ funext (ι i  ) f f' feq refl = feq refl
from-IEq-algᶜ funext (σ A D) f f' feq (a , es) =
  from-IEq-algᶜ funext (D a) (curry f a) (curry f' a) (curry feq a) es
from-IEq-algᶜ funext (ρ D E) f f' feq (ns , ns' , es , es') =
  from-IEq-algᶜ funext E (curry f ns) (curry f' ns')
    (λ ns'' → trans (cong (f ∘ (_, ns'')) (from-IEq-algʳ funext D es))
                    (feq (ns' , ns''))) es'

from-IEq-algᶜˢ :
    FunExt → {I : Set ℓⁱ} (D : ConDs I cbs)
    {N : Carrierᶜˢ D ℓ} (f : Algᶜˢ D N)
  → Algᶜˢ ⌊ IEqODᶜˢ D f ⌋ᶜˢ (λ i → let (_ , n , n' , _) = i in n ≡ n')
from-IEq-algᶜˢ funext (D ∷ Ds) f (inl es) =
  from-IEq-algᶜ funext D (f ∘ inl) (f ∘ inl) (λ _ → refl) es
from-IEq-algᶜˢ funext (D ∷ Ds) f (inr es) = from-IEq-algᶜˢ funext Ds (f ∘ inr) es

from-IEq-alg : ∀ {D N} (C : DataC D N) → FunExt
             → ∀ℓ _ λ ℓs → ∀ᵐᵗ false _ λ ps → Algebraᵈ (IEqD C) ℓs ps _
from-IEq-alg {D} C funext $$ ℓs $$ ps = record
  { Carrier = λ i → let (_ , n , n' , _) = i in n ≡ n'
  ; apply = let Dᶜˢ = PDataD.applyP (DataD.applyL D ℓs) ps
            in  from-IEq-algᶜˢ funext Dᶜˢ (DataC.toN C) }
