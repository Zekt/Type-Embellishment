{-# OPTIONS --safe #-}

module Generics.Safe.RecursionScheme where

open import Prelude
open import Generics.Safe.Telescope; open ∀ℓ; open ∀ᵗ
open import Generics.Safe.Description
open import Generics.Safe.Algebra
open import Generics.Safe.Recursion

private variable
  rb  : RecB
  cb  : ConB
  cbs : ConBs

FoldAlgTᶜ : {I : Set ℓⁱ} (D : ConD I cb) → (I → Set ℓ) → Set (max-π cb ⊔ max-σ cb ⊔ ℓ)
FoldAlgTᶜ (ι i  ) X = X i
FoldAlgTᶜ (σ A D) X = (a : A) → FoldAlgTᶜ (D a) X
FoldAlgTᶜ (ρ D E) X = ⟦ D ⟧ʳ X → FoldAlgTᶜ E X

FoldAlgTᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) → (I → Set ℓ)
           → Tel (maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ hasCon? ℓ cbs)
FoldAlgTᶜˢ []       X = []
FoldAlgTᶜˢ (D ∷ Ds) X = FoldAlgTᶜ D X ∷ constω (FoldAlgTᶜˢ Ds X)

FoldAlgTᵖᵈ : ∀ (D : PDataD) ps ℓ → Set _
FoldAlgTᵖᵈ D ps ℓ = {X : ∀ᵗ true (PDataD.Index D ps) λ _ → Set ℓ}
                  → ∀ᵗ true (FoldAlgTᶜˢ (PDataD.applyP D ps) (X $$_)) λ _
                  → Algebraᵖᵈ D ps ℓ

FoldAlgTᵈ : ∀ (D : DataD) ℓs ps ℓ → Set _
FoldAlgTᵈ D ℓs = FoldAlgTᵖᵈ (DataD.applyL D ℓs)

fold-algᶜ : {I : Set ℓⁱ} (D : ConD I cb) {X : Carrierᶜ D ℓ} → FoldAlgTᶜ D X → Algᶜ D X
fold-algᶜ (ι i  ) f refl       = f
fold-algᶜ (σ A D) f (a  , xs ) = fold-algᶜ (D a) (f a ) xs
fold-algᶜ (ρ D E) f (xs , xs') = fold-algᶜ  E    (f xs) xs'

fold-algᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) {X : Carrierᶜˢ D ℓ}
           → ⟦ FoldAlgTᶜˢ D X ⟧ᵗ → Algᶜˢ D X
fold-algᶜˢ []       _        ()
fold-algᶜˢ (D ∷ Ds) (f , fs) (inl xs) = fold-algᶜ  D  f  xs
fold-algᶜˢ (D ∷ Ds) (f , fs) (inr xs) = fold-algᶜˢ Ds fs xs

fold-alg : (D : DataD) → ∀ {ℓ} → ∀ℓ _ λ ℓs → ∀ᵗ false _ λ ps → FoldAlgTᵈ D ℓs ps ℓ
fold-alg D $$ ℓs $$ ps $$ args =
  algebra _ (fold-algᶜˢ (PDataD.applyP (DataD.applyL D ℓs) ps) args)

Homᶜ : {I : Set ℓⁱ} (D : ConD I cb) {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
     → FoldAlgTᶜ D X → FoldAlgTᶜ D Y → (∀ {i} → X i → Y i)
     → ∀ {i} → ⟦ D ⟧ᶜ X i → Set (max-π cb ⊔ ℓʸ)
Homᶜ (ι i  ) x y h _ = h x ≡ y
Homᶜ (σ A D) f g h (a , xs) = Homᶜ (D a) (f a) (g a) h xs
Homᶜ (ρ D E) {X} {Y} f g h (xs , xs') =
  (ys : ⟦ D ⟧ʳ Y) → ExtEqʳ D ys (fmapʳ D h xs) → Homᶜ E (f xs) (g ys) h xs'

Homᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
      → ⟦ FoldAlgTᶜˢ D X ⟧ᵗ → ⟦ FoldAlgTᶜˢ D Y ⟧ᵗ → (∀ {i} → X i → Y i)
      → Tel (maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ maxMap (hasRec? ℓˣ) cbs ⊔
              hasCon? ℓⁱ cbs ⊔ hasCon? ℓʸ cbs)
Homᶜˢ [] fs gs h = []
Homᶜˢ (D ∷ Ds) {X} (f , fs) (g , gs) h =
  (∀ {i} (xs : ⟦ D ⟧ᶜ X i) → Homᶜ D f g h xs) ∷ constω (Homᶜˢ Ds fs gs h)

fold-fusion-algʳ :
    {I : Set ℓⁱ} (D : RecD I rb) {N : I → Set ℓ} {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
    (fold-fs : ∀ {i} → N i → X i) (fold-gs : ∀ {i} → N i → Y i)
  → (h : ∀ {i} → X i → Y i) (ns : ⟦ D ⟧ʳ N) → Allʳ D (λ _ n → h (fold-fs n) ≡ fold-gs n) ns
  → ExtEqʳ D (fmapʳ D fold-gs ns) (fmapʳ D h (fmapʳ D fold-fs ns))
fold-fusion-algʳ (ι i  ) fold-fs fold-gs h n  eq  = sym eq
fold-fusion-algʳ (π A D) fold-fs fold-gs h ns all =
  λ a → fold-fusion-algʳ (D a) fold-fs fold-gs h (ns a) (all a)

fold-fusion-algᶜ :
    {I : Set ℓⁱ} (D : ConD I cb) {N : I → Set ℓ} {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
    (f : FoldAlgTᶜ D X) (g : FoldAlgTᶜ D Y)
    (fold-fs : ∀ {i} → N i → X i) (fold-gs : ∀ {i} → N i → Y i)
  → (h : ∀ {i} → X i → Y i) → (∀ {i} (xs : ⟦ D ⟧ᶜ X i) → Homᶜ D f g h xs)
  → ∀ {i} (ns : ⟦ D ⟧ᶜ N i) → Allᶜ D (λ _ n → h (fold-fs n) ≡ fold-gs n) ns ℓ'
  → h (fold-algᶜ D f (fmapᶜ D fold-fs ns)) ≡ fold-algᶜ D g (fmapᶜ D fold-gs ns)
fold-fusion-algᶜ (ι i  ) x y fold-fs fold-gs h hom refl all = hom refl
fold-fusion-algᶜ (σ A D) f g fold-fs fold-gs h hom (a , ns) all =
  fold-fusion-algᶜ (D a) (f a) (g a) fold-fs fold-gs h (curry hom a) ns all
fold-fusion-algᶜ (ρ D E) f g fold-fs fold-gs h hom (ns , ns') (all , all') =
  fold-fusion-algᶜ E (f (fmapʳ D fold-fs ns)) (g (fmapʳ D fold-gs ns)) fold-fs fold-gs h
    (λ xs → hom (fmapʳ D fold-fs ns , xs) (fmapʳ D fold-gs ns)
                (fold-fusion-algʳ D fold-fs fold-gs h ns all)) ns' all'

fold-fusion-algᶜˢ :
    {I : Set ℓⁱ} (D : ConDs I cbs) {N : I → Set ℓ} {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
    (fs : ⟦ FoldAlgTᶜˢ D X ⟧ᵗ) (gs : ⟦ FoldAlgTᶜˢ D Y ⟧ᵗ)
    (fold-fs : ∀ {i} → N i → X i) (fold-gs : ∀ {i} → N i → Y i)
  → (h : ∀ {i} → X i → Y i) → ⟦ Homᶜˢ D fs gs h ⟧ᵗ
  → ∀ {i} (ns : ⟦ D ⟧ᶜˢ N i) → Allᶜˢ D (λ _ n → h (fold-fs n) ≡ fold-gs n) ns ℓ'
  → h (fold-algᶜˢ D fs (fmapᶜˢ D fold-fs ns)) ≡ fold-algᶜˢ D gs (fmapᶜˢ D fold-gs ns)
fold-fusion-algᶜˢ (D ∷ Ds) (f , _ ) (g , _ ) fold-fs fold-gs h (hom , _) (inl ns) all =
  fold-fusion-algᶜ  D  f  g  fold-fs fold-gs h hom ns all
fold-fusion-algᶜˢ (D ∷ Ds) (_ , fs) (_ , gs) fold-fs fold-gs h (_ , hom) (inr ns) all =
  fold-fusion-algᶜˢ Ds fs gs fold-fs fold-gs h hom ns all

fold-fusion-alg :
  ∀ {D N} (C : DataC D N)
  → (fold : ∀ {ℓ} → ∀ℓ _ λ ℓs → ∀ᵗ false _ λ ps
          → {X : ∀ᵗ true (PDataD.Index (DataD.applyL D ℓs) ps) λ _ → Set ℓ}
          → ∀ᵗ true (FoldAlgTᶜˢ (PDataD.applyP (DataD.applyL D ℓs) ps) (X $$_)) λ _
          → ∀ {is} → N ℓs ps is → X $$ is)
  → (foldC : ∀ {ℓ ℓs ps}
             {X : ∀ᵗ true (PDataD.Index (DataD.applyL D ℓs) ps) λ _ → Set ℓ}
             (fs : ⟦ FoldAlgTᶜˢ (PDataD.applyP (DataD.applyL D ℓs) ps) (X $$_) ⟧ᵗ)
           → AlgebraC C (fold-alg D $$ ℓs $$ ps $$ fs) (fold $$ ℓs $$ ps $$ fs))
  → ∀ℓ _ λ ℓs → ∀ᵗ false _ λ ps →
    let IT  = PDataD.Index  (DataD.applyL D ℓs) ps
        Dᶜˢ = PDataD.applyP (DataD.applyL D ℓs) ps in
    {X : ∀ᵗ true IT λ _ → Set ℓˣ} {Y : ∀ᵗ true IT λ _ → Set ℓʸ}
  → (h : ∀ᵗ false IT λ is → X $$ is → Y $$ is)
  → ∀ᵗ true (FoldAlgTᶜˢ Dᶜˢ (X $$_)) λ f → ∀ᵗ true (FoldAlgTᶜˢ Dᶜˢ (Y $$_)) λ g
  → ∀ᵗ true (Homᶜˢ Dᶜˢ f g (λ {is} → (h $$ is))) λ hom → IndAlgebraᵈ C ℓs ps ℓʸ
(fold-fusion-alg {D = D} C fold foldC $$ ℓs $$ ps) h $$ fs $$ gs $$ hom =
  let Dᶜˢ = PDataD.applyP (DataD.applyL D ℓs) ps in record
  { Carrier = λ is n → (h $$ is) ((fold $$ ℓs $$ ps $$ fs) n) ≡ (fold $$ ℓs $$ ps $$ gs) n
  ; apply = λ {is} ns all →
      let h'      = λ {is} → h $$ is
          fold-fs = λ {is} → (fold $$ ℓs $$ ps $$ fs) {is}
          fold-gs = λ {is} → (fold $$ ℓs $$ ps $$ gs) {is} in
      begin
        h' (fold-fs (DataC.toN C ns))
          ≡⟨ cong h' (foldC fs ns) ⟩
        h' (fold-algᶜˢ Dᶜˢ fs (fmapᶜˢ Dᶜˢ fold-fs ns))
          ≡⟨ fold-fusion-algᶜˢ Dᶜˢ fs gs fold-fs fold-gs h' hom ns all ⟩
        fold-algᶜˢ Dᶜˢ gs (fmapᶜˢ Dᶜˢ fold-gs ns)
          ≡⟨ sym (foldC gs ns) ⟩
        fold-gs (DataC.toN C ns)
      ∎ } where open ≡-Reasoning
