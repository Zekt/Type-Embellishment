{-# OPTIONS --safe --with-K #-}

open import Prelude

module Generics.Ornament.Algebraic.Isomorphism where

open import Generics.Telescope
open import Generics.Description
open import Generics.Algebra
open import Generics.Recursion
open import Generics.Ornament
open import Generics.Ornament.Description
open import Generics.Ornament.Algebraic

private variable
  rb : RecB
  cb : ConB
  cbs cbs' : ConBs

module Finitary where

  forget-remember-invᶜ :
      {I : Set ℓⁱ} (D : ConD I cb) → Finitaryᶜ cb
    → {N : I → Set ℓ} (toN toN' : Algᶜ D N)
      {X : I → Set ℓˣ} (alg : Algᶜ D X) (f : ∀ {i} → N i → X i)
      {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
      (g : ∀ {i x} → N' (i , x , tt) → N i) (r : ∀ {i} (n : N i) → N' (i , f n , tt))
    → ∀ {i} (ns : ⟦ D ⟧ᶜ N i) → Allᶜ D (λ _ n → g (r n) ≡ n) ns ℓ'' → toN ns ≡ toN' ns
    → toN (eraseᶜ ⌈ algODᶜ D alg ⌉ᶜ (fmapᶜ ⌊ algODᶜ D alg ⌋ᶜ g
        (rememberᶜ {ℓ'' = ℓ'''} D alg f {N'} ns (ind-fmapᶜ D r ns)))) ≡ toN' ns
  forget-remember-invᶜ (ι i) fin toN toN' alg f g r refl all toNeq = toNeq
  forget-remember-invᶜ (σ A D) (_ ∷ fin) toN toN' alg f g r (a , ns) all toNeq =
    forget-remember-invᶜ (D a) fin (curry toN a) (curry toN' a) (curry alg a)
      f g r ns all toNeq
  forget-remember-invᶜ (ρ (ι i) E) (refl ∷ fin) toN toN' alg
    f g r (n , ns) (eq , all) toNeq =
    forget-remember-invᶜ E fin (curry toN (g (r n))) (curry toN' n) (curry alg (f n))
      f g r ns all (trans' (cong (λ n' → toN (n' , ns)) eq) toNeq)

  forget-remember-invᶜˢ :
      {I : Set ℓⁱ} (D : ConDs I cbs) → Finitaryᶜˢ cbs → {N : I → Set ℓ} (toN : Algᶜˢ D N)
      {X : I → Set ℓˣ} (alg : Algᶜˢ D X) (f : ∀ {i} → N i → X i)
      {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'} (g : ∀ {i x} → N' (i , x , tt) → N i)
      (r : ∀ {i} (n : N i) → N' (i , f n , tt))
    → ∀ {i} (ns : ⟦ D ⟧ᶜˢ N i) → Allᶜˢ D (λ _ n → g (r n) ≡ n) ns ℓ''
    → toN (eraseᶜˢ ⌈ algODᶜˢ D alg ⌉ᶜˢ (fmapᶜˢ ⌊ algODᶜˢ D alg ⌋ᶜˢ g
        (rememberᶜˢ {ℓ'' = ℓ'''} D alg f {N'} ns (ind-fmapᶜˢ D r ns)))) ≡ toN ns
  forget-remember-invᶜˢ (D ∷ Ds) (fin ∷ _) toN alg f g r (inl ns) all =
    forget-remember-invᶜ D fin (toN ∘ inl) (toN ∘ inl)
      (alg ∘ inl) f g r ns all refl
  forget-remember-invᶜˢ (D ∷ Ds) (_ ∷ fin) toN alg f g r (inr ns) all =
    forget-remember-invᶜˢ Ds fin (toN ∘ inr) (alg ∘ inr) f g r ns all

  remember-forget-invᶜ :
      {I : Set ℓⁱ} (D : ConD I cb) → Finitaryᶜ cb → {X : I → Set ℓˣ} (alg : Algᶜ D X)
      {N : I → Set ℓ} (f : ∀ {i} → N i → X i) {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
      (r : ∀ {i} (n : N i) → N' (i , f n , tt))
      (g : ∀ {i x} → N' (i , x , tt) → N i)
    → ∀ {i x} (ns' : ⟦ ⌊ algODᶜ D alg ⌋ᶜ ⟧ᶜ N' (i , x , tt))
    → Allᶜ ⌊ algODᶜ D alg ⌋ᶜ (λ is n' → let (i' , x' , _) = is in
        (f (g n') , r (g n')) ≡ ((x' , n') ⦂ Σ[ x'' ∈ X i' ] N' (i' , x'' , tt))) ns' ℓ''
    → (alg (fmapᶜ D f (eraseᶜ ⌈ algODᶜ D alg ⌉ᶜ (fmapᶜ ⌊ algODᶜ D alg ⌋ᶜ g ns'))) ,
      rememberᶜ {ℓ'' = ℓ'''} D alg f
        (eraseᶜ ⌈ algODᶜ D alg ⌉ᶜ (fmapᶜ ⌊ algODᶜ D alg ⌋ᶜ g ns'))
          (ind-fmapᶜ D r (eraseᶜ ⌈ algODᶜ D alg ⌉ᶜ (fmapᶜ ⌊ algODᶜ D alg ⌋ᶜ g ns'))))
    ≡ ((x , ns') ⦂ Σ[ x' ∈ X i ] ⟦ ⌊ algODᶜ D alg ⌋ᶜ ⟧ᶜ N' (i , x' , tt))
  remember-forget-invᶜ (ι i) fin alg f r g refl all = refl
  remember-forget-invᶜ (σ A D) (_ ∷ fin) alg f r g (a , ns') all =
    cong (bimap id (a ,_))
         (remember-forget-invᶜ (D a) fin (curry alg a) f r g ns' all)
  remember-forget-invᶜ (ρ (ι i) E) (refl ∷ fin) alg f r g (x , n' , ns') (eq , all) =
    trans (cong (λ p → (alg (fst p , _) , fst p , snd p ,
                        rememberᶜ E (λ y → alg (fst p , y)) f _ (ind-fmapᶜ E r _))) eq)
          (cong (bimap id ((x ,_) ∘ (n' ,_)))
                (remember-forget-invᶜ E fin (curry alg _) f r g ns' all))

  remember-forget-invᶜˢ :
      {I : Set ℓⁱ} (D : ConDs I cbs) → Finitaryᶜˢ cbs → {X : I → Set ℓˣ} (alg : Algᶜˢ D X)
      {N : I → Set ℓ} (f : ∀ {i} → N i → X i) {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
      (r : ∀ {i} (n : N i) → N' (i , f n , tt))
      (g : ∀ {i x} → N' (i , x , tt) → N i)
    → ∀ {i x} (ns' : ⟦ ⌊ algODᶜˢ D alg ⌋ᶜˢ ⟧ᶜˢ N' (i , x , tt))
    → Allᶜˢ ⌊ algODᶜˢ D alg ⌋ᶜˢ (λ is n' → let (i' , x' , _) = is in
        (f (g n') , r (g n')) ≡ ((x' , n') ⦂ Σ[ x'' ∈ X i' ] N' (i' , x'' , tt))) ns' ℓ''
    → (alg (fmapᶜˢ D f (eraseᶜˢ ⌈ algODᶜˢ D alg ⌉ᶜˢ (fmapᶜˢ ⌊ algODᶜˢ D alg ⌋ᶜˢ g ns'))) ,
        rememberᶜˢ {ℓ'' = ℓ′} D alg f
          (eraseᶜˢ ⌈ algODᶜˢ D alg ⌉ᶜˢ (fmapᶜˢ ⌊ algODᶜˢ D alg ⌋ᶜˢ g ns'))
            (ind-fmapᶜˢ D r
              (eraseᶜˢ ⌈ algODᶜˢ D alg ⌉ᶜˢ (fmapᶜˢ ⌊ algODᶜˢ D alg ⌋ᶜˢ g ns'))))
    ≡ ((x , ns') ⦂ Σ[ x' ∈ X i ] ⟦ ⌊ algODᶜˢ D alg ⌋ᶜˢ ⟧ᶜˢ N' (i , x' , tt))
  remember-forget-invᶜˢ (D ∷ Ds) (fin ∷ _) alg f r g (inl ns') all =
    cong (bimap id inl) (remember-forget-invᶜ  D  fin (alg ∘ inl) f r g ns' all)
  remember-forget-invᶜˢ (D ∷ Ds) (_ ∷ fin) alg f r g (inr ns') all =
    cong (bimap id inr) (remember-forget-invᶜˢ Ds fin (alg ∘ inr) f r g ns' all)

choice : {A : Set ℓ} {B : A → Set ℓ'} {R : (a : A) → B a → Set ℓ''}
      → ((a : A) → Σ[ b ∈ B a ] R a b) → Σ[ f ∈ ((a : A) → B a) ] ((a : A) → R a (f a))
choice c = (λ a → fst (c a)) , (λ a → snd (c a))

module FunExt (funext : FunExt) where

  forget-remember-invʳ :
      {I : Set ℓⁱ} (D : RecD I rb) {X : I → Set ℓˣ} {N : I → Set ℓ}
      (f : ∀ {i} → N i → X i) {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
      (g : ∀ {i x} → N' (i , x , tt) → N i)
      (r : ∀ {i} (n : N i) → N' (i , f n , tt))
    → (ns : ⟦ D ⟧ʳ N) → Allʳ D (λ _ n → g (r n) ≡ n) ns
    → eraseʳ ⌈ algODʳ D (fmapʳ D f ns) ⌉ʳ
        (fmapʳ ⌊ algODʳ D (fmapʳ D f ns) ⌋ʳ g
          (rememberʳ D f {N'} ns (ind-fmapʳ D r ns))) ≡ ns
  forget-remember-invʳ (ι i  ) f g r n  eq  = eq
  forget-remember-invʳ (π A D) f g r ns all =
    funext λ a → forget-remember-invʳ (D a) f g r (ns a) (all a)

  forget-remember-invᶜ :
      {I : Set ℓⁱ} (D : ConD I cb) {N : I → Set ℓ} (toN toN' : Algᶜ D N)
    → (∀ {i} {ns ns' : ⟦ D ⟧ᶜ N i} → ns ≡ ns' → toN ns ≡ toN' ns')
    → {X : I → Set ℓˣ} (alg : Algᶜ D X) (f : ∀ {i} → N i → X i)
      {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
      (g : ∀ {i x} → N' (i , x , tt) → N i) (r : ∀ {i} (n : N i) → N' (i , f n , tt))
    → ∀ {i} (ns : ⟦ D ⟧ᶜ N i) → Allᶜ D (λ _ n → g (r n) ≡ n) ns ℓ''
    → toN (eraseᶜ ⌈ algODᶜ D alg ⌉ᶜ (fmapᶜ ⌊ algODᶜ D alg ⌋ᶜ g
        (rememberᶜ {ℓ'' = ℓ'''} D alg f {N'} ns (ind-fmapᶜ D r ns)))) ≡ toN' ns
  forget-remember-invᶜ (ι i) toN toN' toNeq alg f g r refl all = toNeq refl
  forget-remember-invᶜ (σ A D) toN toN' toNeq alg f g r (a , ns) all =
    forget-remember-invᶜ (D a) (curry toN a) (curry toN' a) (toNeq ∘ cong (a ,_))
      (curry alg a) f g r ns all
  forget-remember-invᶜ (ρ D E) toN toN' toNeq alg f g r (ns , ns') (all , all') =
    forget-remember-invᶜ E (curry toN _) (curry toN' _)
      (toNeq ∘ cong₂ _,_ (forget-remember-invʳ D f g r ns all)) (curry alg _) f g r ns' all'

  forget-remember-invᶜˢ :
      {I : Set ℓⁱ} (D : ConDs I cbs) {N : I → Set ℓ} (toN : Algᶜˢ D N)
      {X : I → Set ℓˣ} (alg : Algᶜˢ D X)  (f : ∀ {i} → N i → X i)
      {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'} (g : ∀ {i x} → N' (i , x , tt) → N i)
      (r : ∀ {i} (n : N i) → N' (i , f n , tt))
    → ∀ {i} (ns : ⟦ D ⟧ᶜˢ N i) → Allᶜˢ D (λ _ n → g (r n) ≡ n) ns ℓ''
    → toN (eraseᶜˢ ⌈ algODᶜˢ D alg ⌉ᶜˢ (fmapᶜˢ ⌊ algODᶜˢ D alg ⌋ᶜˢ g
        (rememberᶜˢ {ℓ'' = ℓ'''} D alg f {N'} ns (ind-fmapᶜˢ D r ns)))) ≡ toN ns
  forget-remember-invᶜˢ (D ∷ Ds) toN alg f g r (inl ns) all =
    forget-remember-invᶜ D (toN ∘ inl) (toN ∘ inl) (cong (toN ∘ inl))
      (alg ∘ inl) f g r ns all
  forget-remember-invᶜˢ (D ∷ Ds) toN alg f g r (inr ns) all =
    forget-remember-invᶜˢ Ds (toN ∘ inr) (alg ∘ inr) f g r ns all

  remember-forget-invʳ :
      {I : Set ℓⁱ} (D : RecD I rb) {X : I → Set ℓˣ} {N : I → Set ℓ}
      (f : ∀ {i} → N i → X i) {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
      (r : ∀ {i} (n : N i) → N' (i , f n , tt))
      (g : ∀ {i x} → N' (i , x , tt) → N i)
    → (xs : ⟦ D ⟧ʳ X) (ns' : ⟦ ⌊ algODʳ D xs ⌋ʳ ⟧ʳ N')
    → Allʳ ⌊ algODʳ D xs ⌋ʳ (λ is n' → let (i' , x' , _) = is in
        (f (g n') , r (g n')) ≡ ((x' , n') ⦂ Σ[ x'' ∈ X i' ] N' (i' , x'' , tt))) ns'
    → let ns = eraseʳ ⌈ algODʳ D xs ⌉ʳ (fmapʳ ⌊ algODʳ D xs ⌋ʳ g ns') in
      (fmapʳ D f ns , rememberʳ D f {N'} ns (ind-fmapʳ D r ns))
    ≡ ((xs , ns') ⦂ Σ[ xs' ∈ ⟦ D ⟧ʳ X ] ⟦ ⌊ algODʳ D xs' ⌋ʳ ⟧ʳ N')
  remember-forget-invʳ (ι i  ) f r g x  n'  eq  = eq
  remember-forget-invʳ (π A D) f r g xs ns' all = cong choice
    (funext λ a → remember-forget-invʳ (D a) f r g (xs a) (ns' a) (all a))

  remember-forget-invᶜ :
      {I : Set ℓⁱ} (D : ConD I cb) {X : I → Set ℓˣ} (alg : Algᶜ D X)
      {N : I → Set ℓ} (f : ∀ {i} → N i → X i) {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
      (r : ∀ {i} (n : N i) → N' (i , f n , tt))
      (g : ∀ {i x} → N' (i , x , tt) → N i)
    → ∀ {i x} (ns' : ⟦ ⌊ algODᶜ D alg ⌋ᶜ ⟧ᶜ N' (i , x , tt))
    → Allᶜ ⌊ algODᶜ D alg ⌋ᶜ (λ is n' → let (i' , x' , _) = is in
        (f (g n') , r (g n')) ≡ ((x' , n') ⦂ Σ[ x'' ∈ X i' ] N' (i' , x'' , tt))) ns' ℓ''
    → (alg (fmapᶜ D f (eraseᶜ ⌈ algODᶜ D alg ⌉ᶜ (fmapᶜ ⌊ algODᶜ D alg ⌋ᶜ g ns'))) ,
      rememberᶜ {ℓ'' = ℓ'''} D alg f
        (eraseᶜ ⌈ algODᶜ D alg ⌉ᶜ (fmapᶜ ⌊ algODᶜ D alg ⌋ᶜ g ns'))
          (ind-fmapᶜ D r (eraseᶜ ⌈ algODᶜ D alg ⌉ᶜ (fmapᶜ ⌊ algODᶜ D alg ⌋ᶜ g ns'))))
    ≡ ((x , ns') ⦂ Σ[ x' ∈ X i ] ⟦ ⌊ algODᶜ D alg ⌋ᶜ ⟧ᶜ N' (i , x' , tt))
  remember-forget-invᶜ (ι i) alg f r g refl all = refl
  remember-forget-invᶜ (σ A D) alg f r g (a , ns') all =
    cong (bimap id (a ,_)) (remember-forget-invᶜ (D a) (curry alg a) f r g ns' all)
  remember-forget-invᶜ (ρ D E) alg f r g (xs , ns' , ns'') (all , all') =
    trans (cong (λ p → (alg (fst p , _) , fst p , snd p ,
                        rememberᶜ E (λ y → alg (fst p , y)) f _ (ind-fmapᶜ E r _)))
                (remember-forget-invʳ D f r g xs ns' all))
          (cong (bimap id ((xs ,_) ∘ (ns' ,_)))
                (remember-forget-invᶜ E (curry alg _) f r g ns'' all'))

  remember-forget-invᶜˢ :
      {I : Set ℓⁱ} (D : ConDs I cbs) {X : I → Set ℓˣ} (alg : Algᶜˢ D X)
      {N : I → Set ℓ} (f : ∀ {i} → N i → X i) {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
      (r : ∀ {i} (n : N i) → N' (i , f n , tt))
      (g : ∀ {i x} → N' (i , x , tt) → N i)
    → ∀ {i x} (ns' : ⟦ ⌊ algODᶜˢ D alg ⌋ᶜˢ ⟧ᶜˢ N' (i , x , tt))
    → Allᶜˢ ⌊ algODᶜˢ D alg ⌋ᶜˢ (λ is n' → let (i' , x' , _) = is in
        (f (g n') , r (g n')) ≡ ((x' , n') ⦂ Σ[ x'' ∈ X i' ] N' (i' , x'' , tt))) ns' ℓ''
    → (alg (fmapᶜˢ D f (eraseᶜˢ ⌈ algODᶜˢ D alg ⌉ᶜˢ (fmapᶜˢ ⌊ algODᶜˢ D alg ⌋ᶜˢ g ns'))) ,
       rememberᶜˢ {ℓ'' = ℓ′} D alg f
         (eraseᶜˢ ⌈ algODᶜˢ D alg ⌉ᶜˢ (fmapᶜˢ ⌊ algODᶜˢ D alg ⌋ᶜˢ g ns'))
           (ind-fmapᶜˢ D r (eraseᶜˢ ⌈ algODᶜˢ D alg ⌉ᶜˢ (fmapᶜˢ ⌊ algODᶜˢ D alg ⌋ᶜˢ g ns'))))
    ≡ ((x , ns') ⦂ Σ[ x' ∈ X i ] ⟦ ⌊ algODᶜˢ D alg ⌋ᶜˢ ⟧ᶜˢ N' (i , x' , tt))
  remember-forget-invᶜˢ (D ∷ Ds) alg f r g (inl ns') all =
    cong (bimap id inl) (remember-forget-invᶜ  D  (alg ∘ inl) f r g ns' all)
  remember-forget-invᶜˢ (D ∷ Ds) alg f r g (inr ns') all =
    cong (bimap id inr) (remember-forget-invᶜˢ Ds (alg ∘ inr) f r g ns' all)

forget-remember-inv :
  ∀ {P f} (C : FoldC P f) {N'} (C' : DataC ⌊ AlgOD P ⌋ᵈ N')
  → let forgetP   = forget C' (FoldP.Conv P) ⌈ AlgOD P ⌉ᵈ
        rememberP = remember C C' in
  ∀ {g} (gC : FoldC forgetP g) {r} (rC : IndC rememberP r)
  → Finitary (FoldP.Desc P) ⊎ω FunExt → IndP
forget-remember-inv {P} {f} C {N'} C' {g} gC {r} rC cond =
  let open FoldP P in record
  { Conv    = Conv
  ; #levels = #levels
  ; level   = level
  ; Param   = Param
  ; param   = param
  ; ParamV  = ParamV
  ; ParamN  = ParamN
  ; Carrier = λ _ ps _ n → g _ ps (r _ ps n) ≡ n
  ; algebra = λ ps ns all → let Dᶜˢ = PDataD.applyP (DataD.applyL Desc _) (param ps) in
      begin
        g _ ps (r _ ps (DataC.toN Conv ns))
          ≡⟨ cong (g _ ps) (IndC.equation rC ns) ⟩
        g _ ps (DataC.toN C'
          (subst (λ x → ⟦ ⌊ AlgOD P ⌋ᵈ ⟧ᵈ (N' _ ps) (_ , x , tt))
                 (sym (FoldC.equation C ns))
                 (rememberᶜˢ {ℓ'' = lzero} Dᶜˢ (algebra ps) (f _ ps) ns
                   (ind-fmapᶜˢ Dᶜˢ (r _ ps) ns))))
          ≡⟨ FoldC.equation gC _ ⟩
        DataC.toN Conv
          (eraseᶜˢ ⌈ algODᶜˢ Dᶜˢ (algebra ps) ⌉ᶜˢ
            (fmapᶜˢ ⌊ algODᶜˢ Dᶜˢ (algebra ps) ⌋ᶜˢ (g _ ps)
              (subst (λ x → ⟦ ⌊ algODᶜˢ Dᶜˢ (algebra ps) ⌋ᶜˢ ⟧ᶜˢ (N' _ ps) (_ , x , tt))
                     (sym (FoldC.equation C ns))
                     (rememberᶜˢ {ℓ'' = lzero} Dᶜˢ (algebra ps) (f _ ps) ns
                       (ind-fmapᶜˢ Dᶜˢ (r _ ps) ns)))))
          ≡⟨ cong (DataC.toN Conv)
                  (erase-fmap-subst-lemma ⌈ algODᶜˢ Dᶜˢ (algebra ps) ⌉ᶜˢ (g _ ps) _ _) ⟩
        DataC.toN Conv
          (eraseᶜˢ ⌈ algODᶜˢ Dᶜˢ (algebra ps) ⌉ᶜˢ
            (fmapᶜˢ ⌊ algODᶜˢ Dᶜˢ (algebra ps) ⌋ᶜˢ (g _ ps)
              (rememberᶜˢ {ℓ'' = lzero} Dᶜˢ (algebra ps) (f _ ps) {N' _ ps} ns
                (ind-fmapᶜˢ Dᶜˢ (r _ ps) ns))))
          ≡⟨ [ (λ fin    → Finitary.forget-remember-invᶜˢ Dᶜˢ (fin {_})
                  (DataC.toN Conv) (algebra ps) (f _ ps) (g _ ps) (r _ ps) ns all)
             , (λ funext → FunExt.forget-remember-invᶜˢ (λ {ℓ} {ℓ'} → funext {ℓ} {ℓ'}) Dᶜˢ
                  (DataC.toN Conv) (algebra ps) (f _ ps) (g _ ps) (r _ ps) ns all) ]ω cond ⟩'
        DataC.toN Conv ns
      ∎ }
  where
    open ≡-Reasoning
    erase-fmap-subst-lemma :
      ∀ {I : Set ℓⁱ} {J : I → Set ℓʲ}
        {D : ConDs (Σ[ i ∈ I ] J i × ⊤) cbs} {E : ConDs I cbs'} (O : ConOs fst D E)
        {X : Σ[ i ∈ I ] J i × ⊤ → Set ℓˣ} {Y : I → Set ℓʸ} (f : ∀ {i j} → X (i , j) → Y i)
        {i j} (xs : ⟦ D ⟧ᶜˢ X (i , j , tt)) {j'} (jeq : j ≡ j')
      → eraseᶜˢ O (fmapᶜˢ D f (subst (λ j' → ⟦ D ⟧ᶜˢ X (i , j' , tt)) jeq xs))
      ≡ eraseᶜˢ O (fmapᶜˢ D f xs)
    erase-fmap-subst-lemma O f xs refl = refl

remember-forget-inv :
  ∀ {P f} (C : FoldC P f) {N'} (C' : DataC ⌊ AlgOD P ⌋ᵈ N')
  → let forgetP   = forget C' (FoldP.Conv P) ⌈ AlgOD P ⌉ᵈ
        rememberP = remember C C' in
  ∀ {g} (gC : FoldC forgetP g) {r} (rC : IndC rememberP r)
  → Finitary (FoldP.Desc P) ⊎ω FunExt → IndP
remember-forget-inv {P} {f} C {N'} C' {g} gC {r} rC cond =
  let open FoldP P in record
  { Conv    = C'
  ; #levels = #levels
  ; level   = id
  ; Param   = Param
  ; param   = id
  ; ParamV  = constTelInfo hidden
  ; ParamN  = ParamN
  ; Carrier = λ ℓs ps (is , x , _) n' →
        (f _ ps (g _ ps n') , r _ ps (g _ ps n'))
      ≡ ((x , n') ⦂ Σ[ x' ∈ Carrier ℓs ps is ] N' ℓs ps (is , x' , tt))
  ; algebra = λ ps ns' all → let Dᶜˢ = PDataD.applyP (DataD.applyL Desc _) (param ps) in
      begin
        (let n = g _ ps (DataC.toN C' ns') in f _ ps n , r _ ps n)
          ≡⟨ cong (λ n → f _ ps n , r _ ps n) (FoldC.equation gC ns') ⟩
        let ns = eraseᵈ ⌈ AlgOD P ⌉ᵈ (fmapᵈ ⌊ AlgOD P ⌋ᵈ (g _ ps) ns')
            n  = DataC.toN Conv ns in
       (f _ ps n , r _ ps n
          ≡⟨ cong (λ m → f _ ps (DataC.toN Conv ns) , m) (IndC.equation rC _) ⟩
        f _ ps n ,
        DataC.toN C'
          (subst (λ x → ⟦ ⌊ AlgOD P ⌋ᵈ ⟧ᵈ (N' _ ps) (_ , x , tt))
                 (sym (FoldC.equation C _))
                 (rememberᶜˢ Dᶜˢ (algebra ps) (f _ ps) _ (ind-fmapᵈ Desc (r _ ps) ns)))
          ≡⟨ pair-subst-lemma (DataC.toN C') (sym (FoldC.equation C _)) ⟩
        algebra ps (fmapᵈ Desc (f _ ps) ns) ,
        DataC.toN C' (rememberᶜˢ Dᶜˢ (algebra ps) (f _ ps) _ (ind-fmapᵈ Desc (r _ ps) ns))
          ≡⟨ cong (bimap id (DataC.toN C'))
                  ([ (λ fin    → Finitary.remember-forget-invᶜˢ Dᶜˢ (fin {_})
                                   (algebra ps) (f _ ps) (r _ ps) (g _ ps) ns' all)
                   , (λ funext → FunExt.remember-forget-invᶜˢ
                                   (λ {ℓ} {ℓ'} → funext {ℓ} {ℓ'}) Dᶜˢ
                                   (algebra ps) (f _ ps) (r _ ps) (g _ ps) ns' all) ]ω cond) ⟩
        (_ , DataC.toN C' ns')
      ∎) }
  where
    open ≡-Reasoning
    pair-subst-lemma :
        {I : Set ℓⁱ} {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
        (f : ∀ {i} → X i → Y i) {i i' : I} (ieq : i ≡ i') {x : X i}
      → (i' , f (subst X ieq x)) ≡ (i , f x)
    pair-subst-lemma f refl = refl
