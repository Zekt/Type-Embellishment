{-# OPTIONS --safe #-}

module Generics.Safe.Ornament.Algebraic.Isomorphism where

open import Prelude
open import Generics.Safe.Telescope; open ∀ℓ; open ∀ᵐᵗ
open import Generics.Safe.Description
open import Generics.Safe.Algebra
open import Generics.Safe.Recursion
open import Generics.Safe.Ornament
open import Generics.Safe.Ornament.Description
open import Generics.Safe.Ornament.Algebraic
open import Generics.Safe.InductiveEquality

private variable
  rb       : RecB
  cb       : ConB
  cbs cbs' : ConBs

forget-remember-invʳ :
    {I : Set ℓⁱ} (D : RecD I rb) {X : I → Set ℓˣ} {N : I → Set ℓ}
    (fold : ∀ {i} → N i → X i) {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
    (forget : ∀ {is} → N' is → N (fst is))
    (remember : ∀ {i} (n : N i) → N' (i , fold n , tt))
    {E : Σ[ i ∈ I ] N i × N i × ⊤ → Set ℓᵉ}
    (ns : ⟦ D ⟧ʳ N) → Allʳ D (λ i' n → E (i' , forget (remember n) , n , tt)) ns
  → ⟦ ⌊ IEqODʳ D (eraseʳ ⌈ algODʳ D (fmapʳ D fold ns) ⌉ʳ
                 (fmapʳ  ⌊ algODʳ D (fmapʳ D fold ns) ⌋ʳ forget
                 (rememberʳ D fold {N'} ns (ind-fmapʳ D remember ns)))) ns ⌋ʳ ⟧ʳ E
forget-remember-invʳ (ι i  ) fold forget remember n  e   = e
forget-remember-invʳ (π A D) fold forget remember ns all =
  λ a → forget-remember-invʳ (D a) fold forget remember (ns a) (all a)

forget-remember-invᶜ :
    {I : Set ℓⁱ} (D : ConD I cb) {X : I → Set ℓˣ} (f : Algᶜ D X)
    {N : I → Set ℓ} (toNL toNR : ∀ {i} → ⟦ D ⟧ᶜ N i → N i)
    (fold : ∀ {i} → N i → X i) {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
    (forget : ∀ {is} → N' is → N (fst is))
    (remember : ∀ {i} (n : N i) → N' (i , fold n , tt))
    {E : Σ[ i ∈ I ] N i × N i × ⊤ → Set ℓᵉ}
  → ∀ {i} (ns : ⟦ D ⟧ᶜ N i)
  → Allᶜ D (λ i' n → E (i' , forget (remember n) , n , tt)) ns ℓ''
  → ⟦ ⌊ IEqODᶜ D toNL toNR ⌋ᶜ ⟧ᶜ E (i ,
      toNL (eraseᶜ ⌈ algODᶜ D f ⌉ᶜ
           (fmapᶜ ⌊ algODᶜ D f ⌋ᶜ forget
           (rememberᶜ {ℓ'' = ℓ′} D f fold {N'} ns (ind-fmapᶜ D remember ns)))) ,
      toNR ns , tt)
forget-remember-invᶜ (ι i  ) f toNL toNR fold forget remember refl all = refl
forget-remember-invᶜ (σ A D) f toNL toNR fold forget remember (a , ns) all =
  a , forget-remember-invᶜ (D a) (curry f a) (curry toNL a) (curry toNR a)
        fold forget remember ns all
forget-remember-invᶜ (ρ D E) f toNL toNR fold forget remember (ns , ns') (all , all') =
  eraseʳ ⌈ algODʳ D (fmapʳ D fold ns) ⌉ʳ
    (fmapʳ ⌊ algODʳ D (fmapʳ D fold ns) ⌋ʳ forget
    (rememberʳ D fold ns (ind-fmapʳ D remember ns))) , ns ,
  forget-remember-invʳ D fold forget remember ns all ,
  forget-remember-invᶜ E (curry f (fmapʳ D fold ns))
    (curry toNL _) (curry toNR _) fold forget remember ns' all'

forget-remember-invᶜˢ :
    {I : Set ℓⁱ} (D : ConDs I cbs) {X : I → Set ℓˣ} (f : Algᶜˢ D X)
    {N : I → Set ℓ} (toN : ∀ {i} → ⟦ D ⟧ᶜˢ N i → N i) (fold : ∀ {i} → N i → X i)
    {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
    (forget : ∀ {is} → N' is → N (fst is))
    (remember : ∀ {i} (n : N i) → N' (i , fold n , tt))
    {E : Σ[ i ∈ I ] N i × N i × ⊤ → Set ℓᵉ}
  → ∀ {i} (ns : ⟦ D ⟧ᶜˢ N i)
  → Allᶜˢ D (λ i' n → E (i' , forget (remember n) , n , tt)) ns ℓ''
  → ⟦ ⌊ IEqODᶜˢ D toN ⌋ᶜˢ ⟧ᶜˢ E (i ,
      toN (eraseᶜˢ ⌈ algODᶜˢ D f ⌉ᶜˢ
          (fmapᶜˢ ⌊ algODᶜˢ D f ⌋ᶜˢ forget
          (rememberᶜˢ {ℓ'' = ℓ′} D f fold {N'} ns (ind-fmapᶜˢ D remember ns)))) ,
      toN ns , tt)
forget-remember-invᶜˢ (D ∷ Ds) f toN fold forget remember (inl ns) all =
  inl (forget-remember-invᶜ D (f ∘ inl) (toN ∘ inl) (toN ∘ inl) fold forget remember ns all)
forget-remember-invᶜˢ (D ∷ Ds) f toN fold forget remember (inr ns) all =
  inr (forget-remember-invᶜˢ Ds (f ∘ inr) (toN ∘ inr) fold forget remember ns all)

erase-fmap-subst-lemma :
  ∀ {I : Set ℓⁱ} {J : I → Set ℓʲ}
    {D : ConDs (Σ[ i ∈ I ] J i × ⊤) cbs} {E : ConDs I cbs'} (O : ConOs fst D E)
    {X : Σ[ i ∈ I ] J i × ⊤ → Set ℓˣ} {Y : I → Set ℓʸ} (f : ∀ {ij} → X ij → Y (fst ij))
    {i j} (xs : ⟦ D ⟧ᶜˢ X (i , j , tt)) {j'} (jeq : j ≡ j')
  → eraseᶜˢ O (fmapᶜˢ D f (subst (λ j' → ⟦ D ⟧ᶜˢ X (i , j' , tt)) jeq xs))
  ≡ eraseᶜˢ O (fmapᶜˢ D f xs)
erase-fmap-subst-lemma O f xs refl = refl

forget-remember-inv-alg :
  ∀ {D N} (C : DataC D N) {ℓf : DataD.Levels D → Level}
    (alg : Algebrasᵗ D ℓf) (fold : FoldsTᵗ C alg) (foldC : AlgebrasCᵗ C alg fold)
  → ∀ {N'} (C' : DataC ⌊ algOD D alg ⌋ᵈ N')
  → (forget : FoldsTᵗ C' (forget-alg ⌈ algOD D alg ⌉ᵈ (DataC.toN C)))
  → AlgebrasCᵗ C' (forget-alg ⌈ algOD D alg ⌉ᵈ (DataC.toN C)) forget
  → (remember : IndsTᵗ C (remember-alg C alg fold foldC C'))
  → IndAlgebrasCᵗ C (remember-alg C alg fold foldC C') remember
  → ∀ {E} → DataC (IEqD D (DataC.toN C)) E → IndAlgebrasᵗ C _
forget-remember-inv-alg {D} {N} C alg fold foldC {N'} C'
  forget forgetC remember rememberC {E} EC $$ ℓs $$ ps =
  let fold'     = λ {is} → (fold     $$ ℓs $$ ps) {is}
      forget'   = λ {is} → (forget   $$ ℓs $$ ps) {is}
      remember' = λ {is} → (remember $$ ℓs $$ ps) {is} in record
  { Carrier = λ is n → E ℓs ps (is , forget' (remember' n) , n , tt)
  ; apply = λ ns all → let Dᶜˢ = PDataD.applyP (DataD.applyL D ℓs) ps in
      subst (λ n → E ℓs ps (_ , n , DataC.toN C ns , tt)) (sym
     (begin
        forget' (remember' (DataC.toN C ns))
          ≡⟨ cong forget' (rememberC ns) ⟩
        forget' (DataC.toN C'
          (subst (λ x → ⟦ ⌊ algOD D alg ⌋ᵈ ⟧ᵈ (N' ℓs ps) (_ , x , tt))
                 (sym (foldC ns))
                 (rememberᶜˢ {ℓ'' = lzero} Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps)) fold'
                    ns (ind-fmapᶜˢ Dᶜˢ remember' ns))))
          ≡⟨ forgetC _ ⟩
        DataC.toN C
          (eraseᶜˢ ⌈ algODᶜˢ Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps)) ⌉ᶜˢ
          (fmapᶜˢ ⌊ algODᶜˢ Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps)) ⌋ᶜˢ forget'
          (subst (λ x → ⟦ ⌊ algODᶜˢ Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps)) ⌋ᶜˢ ⟧ᶜˢ
                          (N' ℓs ps) (_ , x , tt))
                 (sym (foldC ns))
                 (rememberᶜˢ {ℓ'' = lzero} Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps)) fold'
                    ns (ind-fmapᶜˢ Dᶜˢ remember' ns)))))
          ≡⟨ cong (DataC.toN C)
                  (erase-fmap-subst-lemma
                     ⌈ algODᶜˢ Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps)) ⌉ᶜˢ forget' _ _) ⟩
        DataC.toN C
          (eraseᶜˢ ⌈ algODᶜˢ Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps)) ⌉ᶜˢ
          (fmapᶜˢ ⌊ algODᶜˢ Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps)) ⌋ᶜˢ forget'
                 (rememberᶜˢ {ℓ'' = lzero} Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps)) fold'
                    {N' ℓs ps} ns (ind-fmapᶜˢ Dᶜˢ remember' ns))))
      ∎)) (DataC.toN EC
      (forget-remember-invᶜˢ Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps)) (DataC.toN C)
         fold' forget' remember' ns all)) } where open ≡-Reasoning
