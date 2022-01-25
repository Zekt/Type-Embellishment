{-# OPTIONS --safe --without-K #-}

open import Prelude

module Generics.RecursionScheme where

open import Generics.Telescope
open import Generics.Description
open import Generics.Algebra
open import Generics.Recursion

private variable
  rb  : RecB
  cb  : ConB
  cbs : ConBs

FoldOpTᶜ : {I : Set ℓⁱ} (D : ConD I cb) → (I → Set ℓ) → Set (max-π cb ⊔ max-σ cb ⊔ ℓ)
FoldOpTᶜ (ι i  ) X = X i
FoldOpTᶜ (σ A D) X = (a : A) → FoldOpTᶜ (D a) X
FoldOpTᶜ (ρ D E) X = ⟦ D ⟧ʳ X → FoldOpTᶜ E X

FoldOpTelᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) → (I → Set ℓ)
            → Tel (maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ hasCon? ℓ cbs)
FoldOpTelᶜˢ []       X = []
FoldOpTelᶜˢ (D ∷ Ds) X = [ _ ∶ FoldOpTᶜ D X ] FoldOpTelᶜˢ Ds X

fold-opᶜ : {I : Set ℓⁱ} (D : ConD I cb) {X : Carrierᶜ D ℓ} → FoldOpTᶜ D X → Algᶜ D X
fold-opᶜ (ι i  ) f refl       = f
fold-opᶜ (σ A D) f (a  , xs ) = fold-opᶜ (D a) (f a ) xs
fold-opᶜ (ρ D E) f (xs , xs') = fold-opᶜ  E    (f xs) xs'

fold-opᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) {X : Carrierᶜˢ D ℓ}
          → ⟦ FoldOpTelᶜˢ D X ⟧ᵗ → Algᶜˢ D X
fold-opᶜˢ (D ∷ Ds) (f , fs) (inl xs) = fold-opᶜ  D  f  xs
fold-opᶜˢ (D ∷ Ds) (f , fs) (inr xs) = fold-opᶜˢ Ds fs xs

fold-operator : ∀ {D N} → DataC D N → FoldP
fold-operator {D} C = record
  { Conv    = C
  ; #levels = suc (DataD.#levels D)
  ; level   = snd
  ; Param   = λ (ℓ , ℓs) → let Dᵖ = DataD.applyL D ℓs in
      [[ ps ∶ PDataD.Param Dᵖ ]]
      [  X  ∶ Curriedᵗ (PDataD.Index Dᵖ ps) (constTelInfo visible) (λ _ → Set ℓ) ]
              FoldOpTelᶜˢ (PDataD.applyP Dᵖ ps) (uncurryᵗ X)
  ; param   = fst
  ; ParamV  = constTelInfo hidden ++ λ _ → hidden ∷ λ _ → constTelInfo visible
  ; ParamN  = constTelInfo "p" ++ λ _ → "X" ∷ λ _ → constTelInfo "alg"
  ; Carrier = λ _ (_ , X , _) → uncurryᵗ X
  ; algebra = λ (ps , _ , args) → fold-opᶜˢ (PDataD.applyP (DataD.applyL D _) ps) args }

Homᶜ : {I : Set ℓⁱ} (D : ConD I cb) {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
     → FoldOpTᶜ D X → FoldOpTᶜ D Y → (∀ {i} → X i → Y i)
     → ∀ {i} → ⟦ D ⟧ᶜ X i → Set (max-π cb ⊔ ℓʸ)
Homᶜ (ι i  ) x y h _ = h x ≡ y
Homᶜ (σ A D) f g h (a , xs) = Homᶜ (D a) (f a) (g a) h xs
Homᶜ (ρ D E) {X} {Y} f g h (xs , xs') =
  (ys : ⟦ D ⟧ʳ Y) → ExtEqʳ D ys (fmapʳ D h xs) → Homᶜ E (f xs) (g ys) h xs'

∀ᶜ : {I : Set ℓⁱ} (D : ConD I cb) {X : Carrierᶜ D ℓˣ}
   → (∀ {i} → ⟦ D ⟧ᶜ X i → Set ℓʸ) → Set (max-π cb ⊔ max-σ cb ⊔ hasRec? ℓˣ cb ⊔ ℓʸ)
∀ᶜ (ι i  )     Y = Y refl
∀ᶜ (σ A D)     Y = (a : A) → ∀ᶜ (D a) (curry Y a)
∀ᶜ (ρ D E) {X} Y = (xs : ⟦ D ⟧ʳ X) → ∀ᶜ E (curry Y xs)

∀ᶜ-apply : {I : Set ℓⁱ} (D : ConD I cb)
           {X : Carrierᶜ D ℓˣ} {Y : ∀ {i} → ⟦ D ⟧ᶜ X i → Set ℓʸ}
         → ∀ᶜ D Y → ∀ {i} (xs : ⟦ D ⟧ᶜ X i) → Y xs
∀ᶜ-apply (ι i  ) y refl       = y
∀ᶜ-apply (σ A D) f (a ,  xs ) = ∀ᶜ-apply (D a) (f a) xs
∀ᶜ-apply (ρ D E) f (xs , xs') = ∀ᶜ-apply E (f xs) xs'

Homᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
      → ⟦ FoldOpTelᶜˢ D X ⟧ᵗ → ⟦ FoldOpTelᶜˢ D Y ⟧ᵗ → (∀ {i} → X i → Y i)
      → Tel (maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ maxMap (hasRec? ℓˣ) cbs ⊔ hasCon? ℓʸ cbs)
Homᶜˢ []       _        _        h = []
Homᶜˢ (D ∷ Ds) (f , fs) (g , gs) h = [ _ ∶ ∀ᶜ D (Homᶜ D f g h) ] Homᶜˢ Ds fs gs h

fold-fusionʳ :
    {I : Set ℓⁱ} (D : RecD I rb) {N : I → Set ℓ} {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
    (fold-fs : ∀ {i} → N i → X i) (fold-gs : ∀ {i} → N i → Y i)
  → (h : ∀ {i} → X i → Y i) (ns : ⟦ D ⟧ʳ N) → Allʳ D (λ _ n → h (fold-fs n) ≡ fold-gs n) ns
  → ExtEqʳ D (fmapʳ D fold-gs ns) (fmapʳ D h (fmapʳ D fold-fs ns))
fold-fusionʳ (ι i  ) fold-fs fold-gs h n  eq  = sym eq
fold-fusionʳ (π A D) fold-fs fold-gs h ns all =
  λ a → fold-fusionʳ (D a) fold-fs fold-gs h (ns a) (all a)

fold-fusionᶜ :
    {I : Set ℓⁱ} (D : ConD I cb) {N : I → Set ℓ} {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
    (f : FoldOpTᶜ D X) (g : FoldOpTᶜ D Y)
    (fold-fs : ∀ {i} → N i → X i) (fold-gs : ∀ {i} → N i → Y i)
  → (h : ∀ {i} → X i → Y i) → (∀ {i} (xs : ⟦ D ⟧ᶜ X i) → Homᶜ D f g h xs)
  → ∀ {i} (ns : ⟦ D ⟧ᶜ N i) → Allᶜ D (λ _ n → h (fold-fs n) ≡ fold-gs n) ns ℓ'
  → h (fold-opᶜ D f (fmapᶜ D fold-fs ns)) ≡ fold-opᶜ D g (fmapᶜ D fold-gs ns)
fold-fusionᶜ (ι i  ) x y fold-fs fold-gs h hom refl all = hom refl
fold-fusionᶜ (σ A D) f g fold-fs fold-gs h hom (a , ns) all =
  fold-fusionᶜ (D a) (f a) (g a) fold-fs fold-gs h (curry hom a) ns all
fold-fusionᶜ (ρ D E) f g fold-fs fold-gs h hom (ns , ns') (all , all') =
  fold-fusionᶜ E (f (fmapʳ D fold-fs ns)) (g (fmapʳ D fold-gs ns)) fold-fs fold-gs h
    (λ xs → hom (fmapʳ D fold-fs ns , xs) (fmapʳ D fold-gs ns)
                (fold-fusionʳ D fold-fs fold-gs h ns all)) ns' all'

fold-fusionᶜˢ :
    {I : Set ℓⁱ} (D : ConDs I cbs) {N : I → Set ℓ} {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
    (fs : ⟦ FoldOpTelᶜˢ D X ⟧ᵗ) (gs : ⟦ FoldOpTelᶜˢ D Y ⟧ᵗ)
    (fold-fs : ∀ {i} → N i → X i) (fold-gs : ∀ {i} → N i → Y i)
  → (h : ∀ {i} → X i → Y i) → ⟦ Homᶜˢ D fs gs h ⟧ᵗ
  → ∀ {i} (ns : ⟦ D ⟧ᶜˢ N i) → Allᶜˢ D (λ _ n → h (fold-fs n) ≡ fold-gs n) ns ℓ'
  → h (fold-opᶜˢ D fs (fmapᶜˢ D fold-fs ns)) ≡ fold-opᶜˢ D gs (fmapᶜˢ D fold-gs ns)
fold-fusionᶜˢ (D ∷ Ds) (f , _ ) (g , _ ) fold-fs fold-gs h (hom , _) (inl ns) all =
  fold-fusionᶜ  D  f  g  fold-fs fold-gs h (∀ᶜ-apply D hom) ns all
fold-fusionᶜˢ (D ∷ Ds) (_ , fs) (_ , gs) fold-fs fold-gs h (_ , hom) (inr ns) all =
  fold-fusionᶜˢ Ds fs gs fold-fs fold-gs h hom ns all

fold-fusion : ∀ {D N} (C : DataC D N) {fold} → FoldC (fold-operator C) fold → IndP
fold-fusion {D} C {fold} foldC = record
  { Conv    = C
  ; #levels = suc (suc (DataD.#levels D))
  ; level   = snd ∘ snd
  ; Param   = λ (ℓˣ , ℓʸ , ℓs) → let Dᵖ = DataD.applyL D ℓs in
      [[ ps ∶ PDataD.Param Dᵖ ]]
      let ITel = PDataD.Index Dᵖ ps; Dᶜˢ = PDataD.applyP Dᵖ ps in
      [  X  ∶ Curriedᵗ ITel (constTelInfo visible) (λ _ → Set ℓˣ) ]
      [  Y  ∶ Curriedᵗ ITel (constTelInfo visible) (λ _ → Set ℓʸ) ]
      [  h  ∶ Curriedᵗ ITel (constTelInfo hidden ) (λ is → uncurryᵗ X is → uncurryᵗ Y is) ]
      [[ fs ∶ FoldOpTelᶜˢ Dᶜˢ (uncurryᵗ X) ]]
      [[ gs ∶ FoldOpTelᶜˢ Dᶜˢ (uncurryᵗ Y) ]]
              Homᶜˢ Dᶜˢ fs gs (λ {is} → uncurryᵗ h is)
  ; param   = fst
  ; ParamV  = constTelInfo hidden ++ λ _ →
              hidden ∷ λ _ → hidden ∷ λ _ → visible ∷ λ _ →
              constTelInfo hidden ++ λ _ → constTelInfo hidden ++ λ _ → constTelInfo visible
  ; ParamN  = constTelInfo "p" ++ λ _ → "X" ∷ λ _ → "Y" ∷ λ _ → "h" ∷ λ _ →
              constTelInfo "f" ++ λ _ → constTelInfo "g" ++ λ _ → constTelInfo "hom"
  ; Carrier = λ _ (ps , X , Y , h , fs , gs , _) is n →
                uncurryᵗ h is (fold _ (ps , X , fs) n) ≡ fold _ (ps , Y , gs) n
  ; algebra = λ (ps , X , Y , h , fs , gs , hom) {is} ns all →
      let Dᶜˢ = PDataD.applyP (DataD.applyL D _) ps in
      begin
        uncurryᵗ h is (fold _ (ps , X , fs) (DataC.toN C ns))
          ≡⟨ cong (uncurryᵗ h is) (FoldC.equation foldC ns) ⟩
        uncurryᵗ h is (fold-opᶜˢ Dᶜˢ fs (fmapᶜˢ Dᶜˢ (fold _ (ps , X , fs)) ns))
          ≡⟨ fold-fusionᶜˢ Dᶜˢ fs gs (fold _ (ps , X , fs)) (fold _ (ps , Y , gs))
               (λ {is} → uncurryᵗ h is) hom ns all ⟩
        fold-opᶜˢ Dᶜˢ gs (fmapᶜˢ Dᶜˢ (fold _ (ps , Y , gs)) ns)
          ≡⟨ sym (FoldC.equation foldC ns) ⟩′
        fold _ (ps , Y , gs) (DataC.toN C ns)
      □ } where open ≡-Reasoning

IndOpTʳ : {I : Set ℓⁱ} (D : RecD I rb) {N : I → Set ℓ} → ⟦ D ⟧ʳ N
        → (∀ i → N i → Set ℓ') → Set (max-ℓ rb ⊔ ℓ')
IndOpTʳ (ι i  ) n  P = P i n
IndOpTʳ (π A D) ns P = (a : A) → IndOpTʳ (D a) (ns a) P

IndOpTᶜ : {I : Set ℓⁱ} (D : ConD I cb) {N : Carrierᶜ D ℓ} → Algᶜ D N
        → (P : IndCarrierᶜ D N ℓ') → Set (max-π cb ⊔ max-σ cb ⊔ hasRec? ℓ cb ⊔ ℓ')
IndOpTᶜ (ι i  )     f P = P i (f refl)
IndOpTᶜ (σ A D)     f P = (a : A) → IndOpTᶜ (D a) (curry f a) P
IndOpTᶜ (ρ D E) {N} f P = (ns : ⟦ D ⟧ʳ N) → IndOpTʳ D ns P → IndOpTᶜ E (curry f ns) P

IndOpTelᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) {N : Carrierᶜˢ D ℓ} → Algᶜˢ D N
           → (P : IndCarrierᶜˢ D N ℓ') → Tel (maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔
                                              maxMap (hasRec? ℓ) cbs ⊔ hasCon? ℓ' cbs)
IndOpTelᶜˢ []       f P = []
IndOpTelᶜˢ (D ∷ Ds) f P = [ _ ∶ IndOpTᶜ D (f ∘ inl) P ] IndOpTelᶜˢ Ds (f ∘ inr) P

ind-opʳ : {I : Set ℓⁱ} (D : RecD I rb) {N : I → Set ℓ} (ns : ⟦ D ⟧ʳ N)
          {P : ∀ i → N i → Set ℓ'} → Allʳ D P ns → IndOpTʳ D ns P
ind-opʳ (ι i  ) n  p   = p
ind-opʳ (π A D) ns all = λ a → ind-opʳ (D a) (ns a) (all a)

ind-opᶜ : {I : Set ℓⁱ} (D : ConD I cb) {N : Carrierᶜ D ℓ} (f : Algᶜ D N)
          {P : IndCarrierᶜ D N ℓ'} → IndOpTᶜ D f P → IndAlgᶜ D f P ℓ''
ind-opᶜ (ι i  ) f p refl        all = p
ind-opᶜ (σ A D) f g (a  , ns )  all = ind-opᶜ (D a) (curry f a) (g a) ns all
ind-opᶜ (ρ D E) f g (ns , ns') (all , all') =
  ind-opᶜ E (curry f ns) (g ns (ind-opʳ D ns all)) ns' all'

ind-opᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) {N : Carrierᶜˢ D ℓ} (f : Algᶜˢ D N)
           {P : IndCarrierᶜˢ D N ℓ'} → ⟦ IndOpTelᶜˢ D f P ⟧ᵗ → IndAlgᶜˢ D f P ℓ''
ind-opᶜˢ (D ∷ Ds) f (g , gs) (inl ps) = ind-opᶜ  D  (f ∘ inl) g  ps
ind-opᶜˢ (D ∷ Ds) f (g , gs) (inr ps) = ind-opᶜˢ Ds (f ∘ inr) gs ps

ind-operator : ∀ {D N} → DataC D N → IndP
ind-operator {D} {N} C = record
  { Conv    = C
  ; #levels = suc (DataD.#levels D)
  ; level   = snd
  ; Param   = λ (ℓ , ℓs) → let Dᵖ = DataD.applyL D ℓs in
      [[ ps ∶ PDataD.Param Dᵖ ]] let Dᶜˢ = PDataD.applyP Dᵖ ps in
      [  P  ∶ Curriedᵗ (PDataD.Index Dᵖ ps) (constTelInfo hidden)
                (λ is → N ℓs ps is → Set ℓ) ]
              IndOpTelᶜˢ Dᶜˢ (DataC.toN C) (uncurryᵗ P)
  ; param   = fst
  ; ParamV  = constTelInfo hidden ++ λ _ → visible ∷ λ _ → constTelInfo visible
  ; ParamN  = constTelInfo "p" ++ λ _ → "P" ∷ λ _ → constTelInfo "ind-case"
  ; Carrier = λ _ (_ , P , _) is n → uncurryᵗ P is n
  ; algebra = λ (ps , P , fs) →
      ind-opᶜˢ (PDataD.applyP (DataD.applyL D _) ps) (DataC.toN C) fs }
