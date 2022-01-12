{-# OPTIONS --safe --with-K #-}

module Generics.SimpleContainer.Any where

open import Prelude
open import Prelude.Sum as Sum
open import Generics.Telescope
open import Generics.Description
open import Generics.Algebra
open import Generics.Recursion
open import Generics.SimpleContainer

private variable
  rb     : RecB
  cb cb' : ConB
  cbs    : ConBs

thereDʳ : {I : Set ℓⁱ} (D : RecD I rb) {N : I → Set ℓ}
        → ⟦ D ⟧ʳ N → RecD (Σ[ i ∈ I ] N i × ⊤) rb
thereDʳ (ι i  ) n  = ι (i , n , tt)
thereDʳ (π A D) ns = π A λ a → thereDʳ (D a) (ns a)

hereConB : ConB → Level → Level → ConB
hereConB []             ℓᵈ ℓ = inl ℓ ∷ []
hereConB (inl ℓ' ∷ cb) ℓᵈ ℓ = inl ℓ' ∷ hereConB cb ℓᵈ ℓ
hereConB (inr rb ∷ cb) ℓᵈ ℓ = inl (max-ℓ rb ⊔ ℓᵈ) ∷ hereConB cb ℓᵈ ℓ

hereDᶜ' : {I : Set ℓⁱ} (D : ConD I cb) {N : Carrierᶜ D ℓᵈ} (toN : Algᶜ D N) (X : Set ℓ)
        → ConD (Σ[ i ∈ I ] N i × ⊤) (hereConB cb ℓᵈ ℓ)
hereDᶜ' (ι i  ) toN X = σ X λ _ → ι (i , toN refl , tt)
hereDᶜ' (σ A D) toN X = σ A λ a → hereDᶜ' (D a) (curry toN a) X
hereDᶜ' (ρ D E) toN X = σ (⟦ D ⟧ʳ _) λ ns → hereDᶜ' E (curry toN ns) X

hereDᶜ : {I : Set ℓⁱ} (D : ConD I cb) (sb : SCᵇ cb) {El : Set ℓᵉ} (sc : SCᶜ D sb El)
         {N : Carrierᶜ D ℓᵈ} (toN : Algᶜ D N) (P : El → Set ℓ)
       → Any (λ x → Σ[ ℓ' ∈ Level ] x ≡ (inl ℓ' , true)) (allToList sb)
       → ConD (Σ[ i ∈ I ] N i × ⊤) (hereConB cb ℓᵈ ℓ)
hereDᶜ (σ A D) (false ∷ sb) sc toN P (there i) =
  σ A λ a → hereDᶜ (D a) sb (sc a) (curry toN a) P i
hereDᶜ (σ A D) (true ∷ sb) (refl ,ωω sc) toN P (here  _) =
  σ A λ a → hereDᶜ' (D a) (curry toN a) (P a)
hereDᶜ (σ A D) (true ∷ sb) (refl ,ωω sc) toN P (there i) =
  σ A λ a → hereDᶜ (D a) sb (sc a) (curry toN a) P i
hereDᶜ (ρ D E) (_ ∷ sb) sc toN P (there i) =
  σ (⟦ D ⟧ʳ _) λ ns → hereDᶜ E sb sc (curry toN ns) P i

hereConBs' : (cb : ConB) → SCᵇ cb → ConB → ConBs
hereConBs' []           _           cb' = []
hereConBs' (inl _ ∷ cb) (false ∷ s) cb' =       hereConBs' cb s cb'
hereConBs' (inl _ ∷ cb) (true  ∷ s) cb' = cb' ∷ hereConBs' cb s cb'
hereConBs' (inr _ ∷ cb) (_     ∷ s) cb' =       hereConBs' cb s cb'

hereDᶜˢ' : (cb : ConB) (s : SCᵇ cb) {I : Set ℓⁱ} {N : I → Set ℓᵈ}
         → (Any (λ x → Σ[ ℓ' ∈ Level ] x ≡ (inl ℓ' , true)) (allToList s)
           → ConD (Σ[ i ∈ I ] N i × ⊤) cb')
         → ConDs (Σ[ i ∈ I ] N i × ⊤) (hereConBs' cb s cb')
hereDᶜˢ' []           _           Ds = []
hereDᶜˢ' (inl _ ∷ cb) (false ∷ s) Ds = hereDᶜˢ' cb s (λ i → Ds (there i))
hereDᶜˢ' (inl _ ∷ cb) (true  ∷ s) Ds = Ds (here (_ , refl))
                                     ∷ hereDᶜˢ' cb s (λ i → Ds (there i))
hereDᶜˢ' (inr _ ∷ cb) (_     ∷ s) Ds = hereDᶜˢ' cb s (λ i → Ds (there i))

hereConBs : (cbs : ConBs) → All SCᵇ cbs → Level → Level → ConBs
hereConBs []         _        ℓ ℓ' = []
hereConBs (cb ∷ cbs) (s ∷ ss) ℓ ℓ' =
  hereConBs' cb s (hereConB cb ℓ ℓ') <> hereConBs cbs ss ℓ ℓ'

hereDᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) (sbs : All SCᵇ cbs) {El : Set ℓᵉ}
          (scs : SCᶜˢ D sbs El) {N : Carrierᶜˢ D ℓᵈ} (toN : Algᶜˢ D N)  (P : El → Set ℓ)
        → ConDs (Σ[ i ∈ I ] N i × ⊤) (hereConBs cbs sbs ℓᵈ ℓ)
hereDᶜˢ [] sbs scs toN P = []
hereDᶜˢ {cbs = cb ∷ _} (D ∷ Ds) (sb ∷ sbs) (sc ,ωω scs) toN P =
  hereDᶜˢ' cb sb (hereDᶜ D sb sc (toN ∘ inl) P) ++ᶜˢ hereDᶜˢ Ds sbs scs (toN ∘ inr) P

thereConB : ConB → Level → RecB → ConB
thereConB []            ℓᵈ rb' = inr rb' ∷ []
thereConB (inl ℓ' ∷ cb) ℓᵈ rb' = inl ℓ' ∷ thereConB cb ℓᵈ rb'
thereConB (inr rb ∷ cb) ℓᵈ rb' = inl (max-ℓ rb ⊔ ℓᵈ) ∷ thereConB cb ℓᵈ rb'

thereDᶜ' : {I : Set ℓⁱ} (D : ConD I cb) {N : I → Set ℓᵈ} (toN : Algᶜ D N)
           (R : RecD I rb) → ⟦ R ⟧ʳ N → ConD (Σ[ i ∈ I ] N i × ⊤) (thereConB cb ℓᵈ rb)
thereDᶜ' (ι i  ) toN R ns = ρ (thereDʳ R ns) (ι (i , toN refl , tt))
thereDᶜ' (σ A D) toN R ns = σ A λ a → thereDᶜ' (D a) (curry toN a) R ns
thereDᶜ' (ρ D E) toN R ns = σ (⟦ D ⟧ʳ _) λ ns' → thereDᶜ' E (curry toN ns') R ns

thereDᶜ : {I : Set ℓⁱ} (D : ConD I cb) {N : I → Set ℓᵈ} (toN : Algᶜ D N)
        → (i : Any (λ x → Σ[ rb ∈ RecB ] (Sum.[ const ⊥ , rb ≡_ ] x)) cb)
        → ConD (Σ[ i ∈ I ] N i × ⊤) (thereConB cb ℓᵈ (fst (snd (lookupAny i))))
thereDᶜ (σ A D) toN (there i) = σ A λ a → thereDᶜ (D a) (curry toN a) i
thereDᶜ (ρ D E) toN (here (rb , refl)) =
                                σ (⟦ D ⟧ʳ _) λ ns → thereDᶜ' E (curry toN ns) D ns
thereDᶜ (ρ D E) toN (there i) = σ (⟦ D ⟧ʳ _) λ ns → thereDᶜ  E (curry toN ns) i

thereConBs' : ConB → ConB → Level → ConBs
thereConBs' []             cb ℓᵈ = []
thereConBs' (inl ℓ' ∷ cb') cb ℓᵈ = thereConBs' cb' cb ℓᵈ
thereConBs' (inr rb ∷ cb') cb ℓᵈ = thereConB cb ℓᵈ rb ∷ thereConBs' cb' cb ℓᵈ

thereDᶜˢ' : (cb' : ConB) {I : Set ℓⁱ} {N : I → Set ℓᵈ}
          → ((i : Any (λ x → Σ[ rb ∈ RecB ] (Sum.[ const ⊥ , rb ≡_ ] x)) cb')
            → ConD (Σ[ i ∈ I ] N i × ⊤) (thereConB cb ℓᵈ (fst (snd (lookupAny i)))))
          → ConDs (Σ[ i ∈ I ] N i × ⊤) (thereConBs' cb' cb ℓᵈ)
thereDᶜˢ' []             Ds = []
thereDᶜˢ' (inl ℓ' ∷ cb') Ds = thereDᶜˢ' cb' (λ i → Ds (there i))
thereDᶜˢ' (inr rb ∷ cb') Ds = Ds (here (rb , refl)) ∷ thereDᶜˢ' cb' (λ i → Ds (there i))

thereConBs : ConBs → Level → ConBs
thereConBs []         ℓᵈ = []
thereConBs (cb ∷ cbs) ℓᵈ = thereConBs' cb cb ℓᵈ <> thereConBs cbs ℓᵈ

thereDᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) {N : Carrierᶜˢ D ℓᵈ} (toN : Algᶜˢ D N)
         → ConDs (Σ[ i ∈ I ] N i × ⊤) (thereConBs cbs ℓᵈ)
thereDᶜˢ [] toN = []
thereDᶜˢ {cbs = cb ∷ _} (D ∷ Ds) toN =
  thereDᶜˢ' cb (thereDᶜ D (toN ∘ inl)) ++ᶜˢ thereDᶜˢ Ds (toN ∘ inr)

AnyDᵖᵈ : (D : PDataD) → SC D → {N : ∀ ps → Carrierᵖᵈ D ps (PDataD.dlevel D)}
       → (∀ {ps} → Algᵖᵈ D (N ps)) → Level → PDataD
AnyDᵖᵈ D S {N} toN ℓ = record
  { alevel = maxMap (uncurry (hasEl? ℓ)) (allToList (SC.pos S))
  ; level-pre-fixed-point = {!  !}
  ; Param  = [[ ps ∶ PDataD.Param D ]] [ P ∶ (SC.El S ps → Set ℓ) ] []
  ; Index  = λ (ps , _) → [[ is ∶ PDataD.Index D ps ]] [ n ∶ N ps is ] []
  ; applyP = λ (ps , P , _) → let Dᶜˢ = PDataD.applyP D ps in
      hereDᶜˢ Dᶜˢ (SC.pos S) (SC.coe S ps) toN P ++ᶜˢ thereDᶜˢ Dᶜˢ toN }

AnyD : ∀ {D N} → DataC D N → SCᵈ D → DataD
AnyD {D} C S = record
  { #levels = suc (DataD.#levels D)
  ; applyL  = λ (ℓ , ℓs) → AnyDᵖᵈ (DataD.applyL D ℓs) (S ℓs) (DataC.toN C) ℓ }
