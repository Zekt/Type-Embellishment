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
hereConB []            ℓᵈ ℓ = inl ℓ ∷ []
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
hereConBs []         _        ℓᵈ ℓ = []
hereConBs (cb ∷ cbs) (s ∷ ss) ℓᵈ ℓ =
  hereConBs' cb s (hereConB cb ℓᵈ ℓ) <> hereConBs cbs ss ℓᵈ ℓ

hereDᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) (sbs : All SCᵇ cbs) {El : Set ℓᵉ}
          (scs : SCᶜˢ D sbs El) {N : Carrierᶜˢ D ℓᵈ} (toN : Algᶜˢ D N) (P : El → Set ℓ)
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

hereConBs'-lemma : (f : ConB → Level) (cb : ConB) (sb : SCᵇ cb) (cb' : ConB)
                 → maxMap f (hereConBs' cb sb cb') ≡ hasEl? (f cb') cb sb
hereConBs'-lemma f []           []           cb' = refl
hereConBs'-lemma f (inl _ ∷ cb) (false ∷ sb) cb' = hereConBs'-lemma f cb sb cb'
hereConBs'-lemma f (inl _ ∷ cb) (true  ∷ sb) cb' = cong (f cb' ⊔_)
                                                  (hereConBs'-lemma f cb sb cb')
hereConBs'-lemma f (inr _ ∷ cb) (_     ∷ sb) cb' = hereConBs'-lemma f cb sb cb'

max-π-hereConB : (cb : ConB) (ℓᵈ ℓ : Level) → max-π (hereConB cb ℓᵈ ℓ) ≡ 0ℓ
max-π-hereConB []            ℓᵈ ℓ = refl
max-π-hereConB (inl ℓ' ∷ cb) ℓᵈ ℓ = max-π-hereConB cb ℓᵈ ℓ
max-π-hereConB (inr rb ∷ cb) ℓᵈ ℓ = max-π-hereConB cb ℓᵈ ℓ

max-π-hereConBs : (cbs : ConBs) (sbs : All SCᵇ cbs) (ℓᵈ ℓ : Level)
                → maxMap max-π (hereConBs cbs sbs ℓᵈ ℓ) ≡ 0ℓ
max-π-hereConBs []         []         ℓᵈ ℓ = refl
max-π-hereConBs (cb ∷ cbs) (sb ∷ sbs) ℓᵈ ℓ =
  begin
    maxMap max-π (hereConBs (cb ∷ cbs) (sb ∷ sbs) ℓᵈ ℓ)
      ≡⟨⟩
    maxMap max-π (hereConBs' cb sb (hereConB cb ℓᵈ ℓ) <> hereConBs cbs sbs ℓᵈ ℓ)
      ≡⟨ maxMap-<> max-π (hereConBs' cb sb (hereConB cb ℓᵈ ℓ)) (hereConBs cbs sbs ℓᵈ ℓ) ⟩
    maxMap max-π (hereConBs' cb sb (hereConB cb ℓᵈ ℓ)) ⊔
    maxMap max-π (hereConBs cbs sbs ℓᵈ ℓ)
      ≡⟨ cong₂ _⊔_ (hereConBs'-lemma max-π cb sb (hereConB cb ℓᵈ ℓ))
                   (max-π-hereConBs cbs sbs ℓᵈ ℓ) ⟩
    hasEl? (max-π (hereConB cb ℓᵈ ℓ)) cb sb
      ≡⟨ hasEl?-bound (max-π (hereConB cb ℓᵈ ℓ)) cb sb (max-π-hereConB cb ℓᵈ ℓ) ⟩
    0ℓ
  ∎ where open ≡-Reasoning

max-σ-hereConB : (cb : ConB) (ℓᵈ ℓ : Level)
               → max-σ (hereConB cb ℓᵈ ℓ) ≡ max-π cb ⊔ max-σ cb ⊔ hasRec? ℓᵈ cb ⊔ ℓ
max-σ-hereConB []            ℓᵈ ℓ = refl
max-σ-hereConB (inl ℓ' ∷ cb) ℓᵈ ℓ = cong (ℓ' ⊔_) (max-σ-hereConB cb ℓᵈ ℓ)
max-σ-hereConB (inr rb ∷ cb) ℓᵈ ℓ = cong (max-ℓ rb ⊔ ℓᵈ ⊔_) (max-σ-hereConB cb ℓᵈ ℓ)

max-σ-hereConBs : (cbs : ConBs) (sbs : All SCᵇ cbs) (ℓᵈ ℓ : Level)
                → maxMap max-σ (hereConBs cbs sbs ℓᵈ ℓ)
                ⊑ maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔
                  ℓᵈ ⊔ maxMap (uncurry (hasEl? ℓ)) (allToList sbs)
max-σ-hereConBs []         []         ℓᵈ ℓ = refl
max-σ-hereConBs (cb ∷ cbs) (sb ∷ sbs) ℓᵈ ℓ =
  let rhs = maxMap max-π (cb ∷ cbs) ⊔ maxMap max-σ (cb ∷ cbs) ⊔
            ℓᵈ ⊔ maxMap (uncurry (hasEl? ℓ)) (allToList (sb ∷ sbs)) in
  begin
    maxMap max-σ (hereConBs (cb ∷ cbs) (sb ∷ sbs) ℓᵈ ℓ) ⊔ rhs
      ≡⟨⟩
    maxMap max-σ (hereConBs' cb sb (hereConB cb ℓᵈ ℓ) <> hereConBs cbs sbs ℓᵈ ℓ) ⊔ rhs
      ≡⟨ cong (rhs ⊔_) (maxMap-<> max-σ (hereConBs' cb sb (hereConB cb ℓᵈ ℓ))
                                        (hereConBs cbs sbs ℓᵈ ℓ)) ⟩
    maxMap max-σ (hereConBs' cb sb (hereConB cb ℓᵈ ℓ)) ⊔
    maxMap max-σ (hereConBs cbs sbs ℓᵈ ℓ) ⊔ rhs
      ≡⟨ cong (max-π cb ⊔ max-σ cb ⊔ hasEl? ℓ cb sb ⊔_) (cong₂ _⊔_
        (hereConBs'-lemma max-σ cb sb (hereConB cb ℓᵈ ℓ)) (max-σ-hereConBs cbs sbs ℓᵈ ℓ)) ⟩
    hasEl? (max-σ (hereConB cb ℓᵈ ℓ)) cb sb ⊔ rhs
      ≡⟨ cong (λ ℓ' → hasEl? ℓ' cb sb ⊔ rhs) (max-σ-hereConB cb ℓᵈ ℓ) ⟩
    hasEl? (max-π cb ⊔ max-σ cb ⊔ hasRec? ℓᵈ cb ⊔ ℓ) cb sb ⊔ rhs
      ≡⟨ cong (rhs ⊔_) (hasEl?-dist-⊔ (max-π cb ⊔ max-σ cb ⊔ hasRec? ℓᵈ cb) ℓ cb sb) ⟩
    hasEl? (max-π cb ⊔ max-σ cb ⊔ hasRec? ℓᵈ cb) cb sb ⊔ rhs
      ≡⟨ cong (rhs ⊔_) (hasEl?-bound (max-π cb ⊔ max-σ cb ⊔ hasRec? ℓᵈ cb) cb sb
                         (cong (max-π cb ⊔ max-σ cb ⊔_) (hasRec?-bound ℓᵈ cb))) ⟩
    rhs
  ∎ where open ≡-Reasoning

AnyD-level-inequality :
    (ℓ ℓᵈ : Level) (cbs : ConBs) (sbs : All SCᵇ cbs)
  → maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ ℓᵈ ≡ ℓᵈ
  → maxMap max-π (hereConBs cbs sbs ℓᵈ ℓ <> thereConBs cbs ℓᵈ) ⊔
    maxMap max-σ (hereConBs cbs sbs ℓᵈ ℓ <> thereConBs cbs ℓᵈ) ⊔
    ℓᵈ ⊔ maxMap (uncurry (hasEl? ℓ)) (allToList sbs)
  ≡ ℓᵈ ⊔ maxMap (uncurry (hasEl? ℓ)) (allToList sbs)
AnyD-level-inequality ℓ ℓᵈ cbs sbs ineq =
  let hcbs = hereConBs cbs sbs ℓᵈ ℓ
      tcbs = thereConBs cbs ℓᵈ
      ℓᵉ   = maxMap (uncurry (hasEl? ℓ)) (allToList sbs) in
  begin
    maxMap max-π (hcbs <> tcbs) ⊔ maxMap max-σ (hcbs <> tcbs) ⊔ ℓᵈ ⊔ ℓᵉ
      ≡⟨ cong (ℓᵈ ⊔ ℓᵉ ⊔_) (cong₂ _⊔_
        (maxMap-<> max-π hcbs tcbs) (maxMap-<> max-σ hcbs tcbs)) ⟩
    maxMap max-π hcbs ⊔ maxMap max-π tcbs ⊔
    maxMap max-σ hcbs ⊔ maxMap max-σ tcbs ⊔ ℓᵈ ⊔ ℓᵉ
      ≡⟨ {!   !} ⟩
    ℓᵈ ⊔ ℓᵉ
  ∎ where open ≡-Reasoning

AnyDᵖᵈ : (D : PDataD) → SC D → {N : ∀ ps → Carrierᵖᵈ D ps (PDataD.dlevel D)}
       → (∀ {ps} → Algᵖᵈ D (N ps)) → Level → PDataD
AnyDᵖᵈ D S {N} toN ℓ = record
  { alevel = maxMap (uncurry (hasEl? ℓ)) (allToList (SC.pos S))
  ; level-inequality = AnyD-level-inequality
      ℓ (PDataD.dlevel D) (PDataD.struct D) (SC.pos S)(PDataD.level-inequality D)
  ; Param  = [[ ps ∶ PDataD.Param D ]] [ P ∶ (SC.El S ps → Set ℓ) ] []
  ; Index  = λ (ps , _) → [[ is ∶ PDataD.Index D ps ]] [ n ∶ N ps is ] []
  ; applyP = λ (ps , P , _) → let Dᶜˢ = PDataD.applyP D ps in
      hereDᶜˢ Dᶜˢ (SC.pos S) (SC.coe S ps) toN P ++ᶜˢ thereDᶜˢ Dᶜˢ toN }

AnyD : ∀ {D N} → DataC D N → SCᵈ D → DataD
AnyD {D} C S = record
  { #levels = suc (DataD.#levels D)
  ; applyL  = λ (ℓ , ℓs) → AnyDᵖᵈ (DataD.applyL D ℓs) (S ℓs) (DataC.toN C) ℓ }
