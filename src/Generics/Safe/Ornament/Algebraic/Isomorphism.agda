{-# OPTIONS --safe #-}

module Generics.Safe.Ornament.Algebraic.Isomorphism where

open import Prelude
open import Generics.Safe.Telescope; open ∀ℓ; open ∀ᵗ
open import Generics.Safe.Description
open import Generics.Safe.Algebra
open import Generics.Safe.Recursion
open import Generics.Safe.Ornament
open import Generics.Safe.Ornament.Description
open import Generics.Safe.Ornament.Algebraic

private variable
  rb : RecB
  cb : ConB
  cbs cbs' : ConBs

erase-fmap-subst-lemma :
  ∀ {I : Set ℓⁱ} {J : I → Set ℓʲ}
    {D : ConDs (Σ[ i ∈ I ] J i × ⊤) cbs} {E : ConDs I cbs'} (O : ConOs fst D E)
    {X : Σ[ i ∈ I ] J i × ⊤ → Set ℓˣ} {Y : I → Set ℓʸ} (f : ∀ {ij} → X ij → Y (fst ij))
    {i j} (xs : ⟦ D ⟧ᶜˢ X (i , j , tt)) {j'} (jeq : j ≡ j')
  → eraseᶜˢ O (fmapᶜˢ D f (subst (λ j' → ⟦ D ⟧ᶜˢ X (i , j' , tt)) jeq xs))
  ≡ eraseᶜˢ O (fmapᶜˢ D f xs)
erase-fmap-subst-lemma O f xs refl = refl

pair-subst-lemma : {I : Set ℓⁱ} {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
                  (f : ∀ {i} → X i → Y i) {i i' : I} (ieq : i ≡ i') {x : X i}
                → (i' , f (subst X ieq x)) ≡ (i , f x)
pair-subst-lemma f refl = refl

module Finitary where

  forget-remember-invᶜ :
      {I : Set ℓⁱ} (D : ConD I cb) → Finitaryᶜ cb
    → {X : I → Set ℓˣ} (f : Algᶜ D X) {N : I → Set ℓ}
      (fold : ∀ {i} → N i → X i) {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
      (forget : ∀ {is} → N' is → N (fst is))
      (remember : ∀ {i} (n : N i) → N' (i , fold n , tt))
    → ∀ {i} (ns : ⟦ D ⟧ᶜ N i) → Allᶜ D (λ _ n → forget (remember n) ≡ n) ns ℓ''
    → eraseᶜ ⌈ algODᶜ D f ⌉ᶜ (fmapᶜ ⌊ algODᶜ D f ⌋ᶜ forget
            (rememberᶜ {ℓ'' = ℓ'''} D f fold {N'} ns (ind-fmapᶜ D remember ns))) ≡ ns
  forget-remember-invᶜ (ι i) fin f fold forget remember refl all = refl
  forget-remember-invᶜ (σ A D) (_ ∷ fin) f fold forget remember (a , ns) all =
    cong (a ,_) (forget-remember-invᶜ (D a) fin (curry f a) fold forget remember ns all)
  forget-remember-invᶜ (ρ (ι i) E) (refl ∷ fin)
    f fold forget remember (_ , ns) (eq , all) =
    cong₂ _,_ eq (forget-remember-invᶜ E fin (curry f _) fold forget remember ns all)

  forget-remember-invᶜˢ :
      {I : Set ℓⁱ} (D : ConDs I cbs) → Finitaryᶜˢ cbs
    → {X : I → Set ℓˣ} (f : Algᶜˢ D X) {N : I → Set ℓ} (fold : ∀ {i} → N i → X i)
      {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'} (forget : ∀ {is} → N' is → N (fst is))
      (remember : ∀ {i} (n : N i) → N' (i , fold n , tt))
    → ∀ {i} (ns : ⟦ D ⟧ᶜˢ N i) → Allᶜˢ D (λ _ n → forget (remember n) ≡ n) ns ℓ''
    → eraseᶜˢ ⌈ algODᶜˢ D f ⌉ᶜˢ (fmapᶜˢ ⌊ algODᶜˢ D f ⌋ᶜˢ forget
      (rememberᶜˢ {ℓ'' = ℓ'''} D f fold {N'} ns (ind-fmapᶜˢ D remember ns))) ≡ ns
  forget-remember-invᶜˢ (D ∷ Ds) (fin ∷ _) f fold forget remember (inl ns) all =
    cong inl (forget-remember-invᶜ  D  fin (f ∘ inl) fold forget remember ns all)
  forget-remember-invᶜˢ (D ∷ Ds) (_ ∷ fin) f fold forget remember (inr ns) all =
    cong inr (forget-remember-invᶜˢ Ds fin (f ∘ inr) fold forget remember ns all)

  forget-remember-inv-alg :
    ∀ {D N} (C : DataC D N) → Finitaryᵈ D → ∀ {ℓf}
      (alg : Algebrasᵗ D ℓf) (fold : FoldsTᵗ C alg) (foldC : AlgebrasCᵗ C alg fold)
    → ∀ {N'} (C' : DataC ⌊ algOD D alg ⌋ᵈ N')
    → (forget : FoldsTᵗ C' (forget-alg ⌈ algOD D alg ⌉ᵈ (DataC.toN C)))
    → AlgebrasCᵗ C' (forget-alg ⌈ algOD D alg ⌉ᵈ (DataC.toN C)) forget
    → (remember : IndsTᵗ C (remember-alg C alg fold foldC C'))
    → IndAlgebrasCᵗ C (remember-alg C alg fold foldC C') remember
    → IndAlgebrasᵗ C _
  forget-remember-inv-alg {D} {N} C fin alg fold foldC {N'} C'
    forget forgetC remember rememberC $$ ℓs $$ ps =
    let fold'     = λ {is} → (fold     $$ ℓs $$ ps) {is}
        forget'   = λ {is} → (forget   $$ ℓs $$ ps) {is}
        remember' = λ {is} → (remember $$ ℓs $$ ps) {is} in record
    { Carrier = λ is n → forget' (remember' n) ≡ n
    ; apply = λ ns all → let Dᶜˢ = PDataD.applyP (DataD.applyL D ℓs) ps in
        begin
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
                      (rememberᶜˢ {ℓ'' = lzero} Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps))
                        fold' ns (ind-fmapᶜˢ Dᶜˢ remember' ns)))))
            ≡⟨ cong (DataC.toN C)
                    (erase-fmap-subst-lemma
                      ⌈ algODᶜˢ Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps)) ⌉ᶜˢ forget' _ _) ⟩
          DataC.toN C
            (eraseᶜˢ ⌈ algODᶜˢ Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps)) ⌉ᶜˢ
            (fmapᶜˢ ⌊ algODᶜˢ Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps)) ⌋ᶜˢ forget'
              (rememberᶜˢ {ℓ'' = lzero} Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps)) fold'
                {N' ℓs ps} ns (ind-fmapᶜˢ Dᶜˢ remember' ns))))
            ≡⟨ cong (DataC.toN C)
                    (forget-remember-invᶜˢ Dᶜˢ (fin ℓs) (Algebra.apply (alg $$ ℓs $$ ps))
                      fold' forget' remember' ns all) ⟩
          DataC.toN C ns
        ∎ } where open ≡-Reasoning

  remember-forget-invᶜ :
      {I : Set ℓⁱ} (D : ConD I cb) → Finitaryᶜ cb → {X : I → Set ℓˣ} (f : Algᶜ D X)
      {N : I → Set ℓ} (fold : ∀ {i} → N i → X i) {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
      (remember : ∀ {i} (n : N i) → N' (i , fold n , tt))
      (forget : ∀ {is} → N' is → N (fst is))
    → ∀ {i x} (ns' : ⟦ ⌊ algODᶜ D f ⌋ᶜ ⟧ᶜ N' (i , x , tt))
    → Allᶜ ⌊ algODᶜ D f ⌋ᶜ (λ is n' → let (i' , x' , _) = is in
          (fold (forget n') , remember (forget n'))
        ≡ ((x' , n') ⦂ Σ[ x'' ∈ X i' ] N' (i' , x'' , tt))) ns' ℓ''
    → (f (fmapᶜ D fold (eraseᶜ ⌈ algODᶜ D f ⌉ᶜ (fmapᶜ ⌊ algODᶜ D f ⌋ᶜ forget ns'))) ,
      rememberᶜ {ℓ'' = ℓ'''} D f fold
        (eraseᶜ ⌈ algODᶜ D f ⌉ᶜ (fmapᶜ ⌊ algODᶜ D f ⌋ᶜ forget ns'))
          (ind-fmapᶜ D remember
            (eraseᶜ ⌈ algODᶜ D f ⌉ᶜ (fmapᶜ ⌊ algODᶜ D f ⌋ᶜ forget ns'))))
    ≡ ((x , ns') ⦂ Σ[ x' ∈ X i ] (⟦ ⌊ algODᶜ D f ⌋ᶜ ⟧ᶜ N' (i , x' , tt)))
  remember-forget-invᶜ (ι i) fin f fold remember forget refl all = refl
  remember-forget-invᶜ (σ A D) (_ ∷ fin) f fold remember forget (a , ns') all =
    cong (bimap id (a ,_))
         (remember-forget-invᶜ (D a) fin (curry f a) fold remember forget ns' all)
  remember-forget-invᶜ (ρ (ι i) E) (refl ∷ fin)
    f fold remember forget (x , n' , ns') (eq , all) =
    trans (cong (λ p → (f (fst p , _) , fst p , snd p ,
                        rememberᶜ E (λ y → f (fst p , y)) fold _ (ind-fmapᶜ E remember _)))
                eq)
          (cong (bimap id ((x ,_) ∘ (n' ,_)))
                (remember-forget-invᶜ E fin (curry f _) fold remember forget ns' all))

  remember-forget-invᶜˢ :
      {I : Set ℓⁱ} (D : ConDs I cbs) → Finitaryᶜˢ cbs → {X : I → Set ℓˣ} (f : Algᶜˢ D X)
      {N : I → Set ℓ} (fold : ∀ {i} → N i → X i) {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
      (remember : ∀ {i} (n : N i) → N' (i , fold n , tt))
      (forget : ∀ {is} → N' is → N (fst is))
    → ∀ {i x} (ns' : ⟦ ⌊ algODᶜˢ D f ⌋ᶜˢ ⟧ᶜˢ N' (i , x , tt))
    → Allᶜˢ ⌊ algODᶜˢ D f ⌋ᶜˢ (λ is n' → let (i' , x' , _) = is in
          (fold (forget n') , remember (forget n'))
        ≡ ((x' , n') ⦂ Σ[ x'' ∈ X i' ] N' (i' , x'' , tt))) ns' ℓ''
    → (f (fmapᶜˢ D fold (eraseᶜˢ ⌈ algODᶜˢ D f ⌉ᶜˢ (fmapᶜˢ ⌊ algODᶜˢ D f ⌋ᶜˢ forget ns'))) ,
      rememberᶜˢ {ℓ'' = ℓ′} D f fold
        (eraseᶜˢ ⌈ algODᶜˢ D f ⌉ᶜˢ (fmapᶜˢ ⌊ algODᶜˢ D f ⌋ᶜˢ forget ns'))
          (ind-fmapᶜˢ D remember
            (eraseᶜˢ ⌈ algODᶜˢ D f ⌉ᶜˢ (fmapᶜˢ ⌊ algODᶜˢ D f ⌋ᶜˢ forget ns'))))
    ≡ ((x , ns') ⦂ Σ[ x' ∈ X i ] (⟦ ⌊ algODᶜˢ D f ⌋ᶜˢ ⟧ᶜˢ N' (i , x' , tt)))
  remember-forget-invᶜˢ (D ∷ Ds) (fin ∷ _) f fold remember forget (inl ns') all =
    cong (bimap id inl)
        (remember-forget-invᶜ  D  fin (f ∘ inl) fold remember forget ns' all)
  remember-forget-invᶜˢ (D ∷ Ds) (_ ∷ fin) f fold remember forget (inr ns') all =
    cong (bimap id inr)
        (remember-forget-invᶜˢ Ds fin (f ∘ inr) fold remember forget ns' all)

  remember-forget-inv-alg :
    ∀ {D N} (C : DataC D N) → Finitaryᵈ D →
    ∀ {ℓf} (alg : Algebrasᵗ D ℓf) (fold : FoldsTᵗ C alg) (foldC : AlgebrasCᵗ C alg fold)
    → ∀ {N'} (C' : DataC ⌊ algOD D alg ⌋ᵈ N')
    → (remember : IndsTᵗ C (remember-alg C alg fold foldC C'))
    → IndAlgebrasCᵗ C (remember-alg C alg fold foldC C') remember
    → (forget : FoldsTᵗ C' (forget-alg ⌈ algOD D alg ⌉ᵈ (DataC.toN C)))
    → AlgebrasCᵗ C' (forget-alg ⌈ algOD D alg ⌉ᵈ (DataC.toN C)) forget
    → IndAlgebrasᵗ C' _
  remember-forget-inv-alg {D} C fin alg fold foldC {N'} C'
    remember rememberC forget forgetC $$ ℓs $$ ps =
    let alg'      = λ {is} → Algebra.apply (alg $$ ℓs $$ ps) {is}
        fold'     = λ {is} → (fold     $$ ℓs $$ ps) {is}
        remember' = λ {is} → (remember $$ ℓs $$ ps) {is}
        forget'   = λ {is} → (forget   $$ ℓs $$ ps) {is} in record
    { Carrier = λ i n' → let (is , x , _) = i in
        (fold' (forget' n') , remember' (forget' n')) ≡ (x , n')
    ; apply = λ ns' all → let Dᶜˢ = PDataD.applyP (DataD.applyL D ℓs) ps in
        begin
          (let n = forget' (DataC.toN C' ns') in fold' n , remember' n)
            ≡⟨ cong (λ n → fold' n , remember' n) (forgetC ns') ⟩
          let ns = eraseᵈ ⌈ algOD D alg ⌉ᵈ (fmapᵈ ⌊ algOD D alg ⌋ᵈ forget' ns')
              n  = DataC.toN C ns in
        (fold' n , remember' n
            ≡⟨ cong (λ m → fold' (DataC.toN C ns) , m) (rememberC _) ⟩
          fold' n ,
          DataC.toN C' (subst (λ x → ⟦ ⌊ algOD D alg ⌋ᵈ ⟧ᵈ (N' ℓs ps) (_ , x , tt))
                              (sym (foldC _))
                              (rememberᶜˢ Dᶜˢ alg' fold' _ (ind-fmapᵈ D remember' ns)))
            ≡⟨ pair-subst-lemma (DataC.toN C') (sym (foldC _)) ⟩
          alg' (fmapᵈ D fold' ns) ,
          DataC.toN C' (rememberᶜˢ Dᶜˢ alg' fold' _ (ind-fmapᵈ D remember' ns))
            ≡⟨ cong (bimap id (DataC.toN C'))
                    (remember-forget-invᶜˢ Dᶜˢ (fin ℓs)
                      alg' fold' remember' forget' ns' all) ⟩
          (_ , DataC.toN C' ns')
        ∎) } where open ≡-Reasoning

choice : {A : Set ℓ} {B : A → Set ℓ'} {R : (a : A) → B a → Set ℓ''}
       → ((a : A) → Σ[ b ∈ B a ] R a b) → Σ[ f ∈ ((a : A) → B a) ] ((a : A) → R a (f a))
choice c = (λ a → fst (c a)) , (λ a → snd (c a))

module FunExt (funext : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (a : A) → B a}
                      → (∀ a → f a ≡ g a) → f ≡ g) where

  forget-remember-invʳ :
      {I : Set ℓⁱ} (D : RecD I rb) {X : I → Set ℓˣ} {N : I → Set ℓ}
      (fold : ∀ {i} → N i → X i) {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
      (forget : ∀ {is} → N' is → N (fst is))
      (remember : ∀ {i} (n : N i) → N' (i , fold n , tt))
    → (ns : ⟦ D ⟧ʳ N) → Allʳ D (λ _ n → forget (remember n) ≡ n) ns
    → eraseʳ ⌈ algODʳ D (fmapʳ D fold ns) ⌉ʳ
        (fmapʳ ⌊ algODʳ D (fmapʳ D fold ns) ⌋ʳ forget
          (rememberʳ D fold {N'} ns (ind-fmapʳ D remember ns))) ≡ ns
  forget-remember-invʳ (ι i  ) fold forget remember n  eq  = eq
  forget-remember-invʳ (π A D) fold forget remember ns all =
    funext λ a → forget-remember-invʳ (D a) fold forget remember (ns a) (all a)

  forget-remember-invᶜ :
      {I : Set ℓⁱ} (D : ConD I cb) {X : I → Set ℓˣ} (f : Algᶜ D X) {N : I → Set ℓ}
      (fold : ∀ {i} → N i → X i) {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
      (forget : ∀ {is} → N' is → N (fst is))
      (remember : ∀ {i} (n : N i) → N' (i , fold n , tt))
    → ∀ {i} (ns : ⟦ D ⟧ᶜ N i) → Allᶜ D (λ _ n → forget (remember n) ≡ n) ns ℓ''
    → eraseᶜ ⌈ algODᶜ D f ⌉ᶜ (fmapᶜ ⌊ algODᶜ D f ⌋ᶜ forget
            (rememberᶜ {ℓ'' = ℓ'''} D f fold {N'} ns (ind-fmapᶜ D remember ns))) ≡ ns
  forget-remember-invᶜ (ι i) f fold forget remember refl all = refl
  forget-remember-invᶜ (σ A D) f fold forget remember (a , ns) all =
    cong (a ,_) (forget-remember-invᶜ (D a) (curry f a) fold forget remember ns all)
  forget-remember-invᶜ (ρ D E) f fold forget remember (ns , ns') (all , all') =
    cong₂ _,_ (forget-remember-invʳ D             fold forget remember ns  all )
              (forget-remember-invᶜ E (curry f _) fold forget remember ns' all')

  forget-remember-invᶜˢ :
      {I : Set ℓⁱ} (D : ConDs I cbs)
    → {X : I → Set ℓˣ} (f : Algᶜˢ D X) {N : I → Set ℓ} (fold : ∀ {i} → N i → X i)
      {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'} (forget : ∀ {is} → N' is → N (fst is))
      (remember : ∀ {i} (n : N i) → N' (i , fold n , tt))
    → ∀ {i} (ns : ⟦ D ⟧ᶜˢ N i) → Allᶜˢ D (λ _ n → forget (remember n) ≡ n) ns ℓ''
    → eraseᶜˢ ⌈ algODᶜˢ D f ⌉ᶜˢ (fmapᶜˢ ⌊ algODᶜˢ D f ⌋ᶜˢ forget
      (rememberᶜˢ {ℓ'' = ℓ'''} D f fold {N'} ns (ind-fmapᶜˢ D remember ns))) ≡ ns
  forget-remember-invᶜˢ (D ∷ Ds) f fold forget remember (inl ns) all =
    cong inl (forget-remember-invᶜ  D  (f ∘ inl) fold forget remember ns all)
  forget-remember-invᶜˢ (D ∷ Ds) f fold forget remember (inr ns) all =
    cong inr (forget-remember-invᶜˢ Ds (f ∘ inr) fold forget remember ns all)

  forget-remember-inv-alg :
    ∀ {D N} (C : DataC D N) {ℓf}
      (alg : Algebrasᵗ D ℓf) (fold : FoldsTᵗ C alg) (foldC : AlgebrasCᵗ C alg fold)
    → ∀ {N'} (C' : DataC ⌊ algOD D alg ⌋ᵈ N')
    → (forget : FoldsTᵗ C' (forget-alg ⌈ algOD D alg ⌉ᵈ (DataC.toN C)))
    → AlgebrasCᵗ C' (forget-alg ⌈ algOD D alg ⌉ᵈ (DataC.toN C)) forget
    → (remember : IndsTᵗ C (remember-alg C alg fold foldC C'))
    → IndAlgebrasCᵗ C (remember-alg C alg fold foldC C') remember
    → IndAlgebrasᵗ C _
  forget-remember-inv-alg {D} {N} C alg fold foldC {N'} C'
    forget forgetC remember rememberC $$ ℓs $$ ps =
    let fold'     = λ {is} → (fold     $$ ℓs $$ ps) {is}
        forget'   = λ {is} → (forget   $$ ℓs $$ ps) {is}
        remember' = λ {is} → (remember $$ ℓs $$ ps) {is} in record
    { Carrier = λ is n → forget' (remember' n) ≡ n
    ; apply = λ ns all → let Dᶜˢ = PDataD.applyP (DataD.applyL D ℓs) ps in
        begin
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
                      (rememberᶜˢ {ℓ'' = lzero} Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps))
                        fold' ns (ind-fmapᶜˢ Dᶜˢ remember' ns)))))
            ≡⟨ cong (DataC.toN C)
                    (erase-fmap-subst-lemma
                      ⌈ algODᶜˢ Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps)) ⌉ᶜˢ forget' _ _) ⟩
          DataC.toN C
            (eraseᶜˢ ⌈ algODᶜˢ Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps)) ⌉ᶜˢ
            (fmapᶜˢ ⌊ algODᶜˢ Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps)) ⌋ᶜˢ forget'
              (rememberᶜˢ {ℓ'' = lzero} Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps)) fold'
                {N' ℓs ps} ns (ind-fmapᶜˢ Dᶜˢ remember' ns))))
            ≡⟨ cong (DataC.toN C)
                    (forget-remember-invᶜˢ Dᶜˢ (Algebra.apply (alg $$ ℓs $$ ps))
                      fold' forget' remember' ns all) ⟩
          DataC.toN C ns
        ∎ } where open ≡-Reasoning

  remember-forget-invʳ :
      {I : Set ℓⁱ} (D : RecD I rb) {X : I → Set ℓˣ} {N : I → Set ℓ}
      (fold : ∀ {i} → N i → X i) {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
      (remember : ∀ {i} (n : N i) → N' (i , fold n , tt))
      (forget : ∀ {is} → N' is → N (fst is))
    → (xs : ⟦ D ⟧ʳ X) (ns' : ⟦ ⌊ algODʳ D xs ⌋ʳ ⟧ʳ N')
    → Allʳ ⌊ algODʳ D xs ⌋ʳ (λ is n' → let (i' , x' , _) = is in
          (fold (forget n') , remember (forget n'))
        ≡ ((x' , n') ⦂ Σ[ x'' ∈ X i' ] N' (i' , x'' , tt))) ns'
    → let ns = eraseʳ ⌈ algODʳ D xs ⌉ʳ (fmapʳ ⌊ algODʳ D xs ⌋ʳ forget ns') in
      (fmapʳ D fold ns , rememberʳ D fold {N'} ns (ind-fmapʳ D remember ns))
    ≡ ((xs , ns') ⦂ Σ[ xs' ∈ ⟦ D ⟧ʳ X ] (⟦ ⌊ algODʳ D xs' ⌋ʳ ⟧ʳ N'))
  remember-forget-invʳ (ι i  ) fold remember forget x  n'  eq  = eq
  remember-forget-invʳ (π A D) fold remember forget xs ns' all = cong choice
    (funext λ a → remember-forget-invʳ (D a) fold remember forget (xs a) (ns' a) (all a))

  remember-forget-invᶜ :
      {I : Set ℓⁱ} (D : ConD I cb) {X : I → Set ℓˣ} (f : Algᶜ D X)
      {N : I → Set ℓ} (fold : ∀ {i} → N i → X i) {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
      (remember : ∀ {i} (n : N i) → N' (i , fold n , tt))
      (forget : ∀ {is} → N' is → N (fst is))
    → ∀ {i x} (ns' : ⟦ ⌊ algODᶜ D f ⌋ᶜ ⟧ᶜ N' (i , x , tt))
    → Allᶜ ⌊ algODᶜ D f ⌋ᶜ (λ is n' → let (i' , x' , _) = is in
          (fold (forget n') , remember (forget n'))
        ≡ ((x' , n') ⦂ Σ[ x'' ∈ X i' ] N' (i' , x'' , tt))) ns' ℓ''
    → (f (fmapᶜ D fold (eraseᶜ ⌈ algODᶜ D f ⌉ᶜ (fmapᶜ ⌊ algODᶜ D f ⌋ᶜ forget ns'))) ,
      rememberᶜ {ℓ'' = ℓ'''} D f fold
        (eraseᶜ ⌈ algODᶜ D f ⌉ᶜ (fmapᶜ ⌊ algODᶜ D f ⌋ᶜ forget ns'))
          (ind-fmapᶜ D remember
            (eraseᶜ ⌈ algODᶜ D f ⌉ᶜ (fmapᶜ ⌊ algODᶜ D f ⌋ᶜ forget ns'))))
    ≡ ((x , ns') ⦂ Σ[ x' ∈ X i ] (⟦ ⌊ algODᶜ D f ⌋ᶜ ⟧ᶜ N' (i , x' , tt)))
  remember-forget-invᶜ (ι i) f fold remember forget refl all = refl
  remember-forget-invᶜ (σ A D) f fold remember forget (a , ns') all =
    cong (bimap id (a ,_))
         (remember-forget-invᶜ (D a) (curry f a) fold remember forget ns' all)
  remember-forget-invᶜ (ρ D E) f fold remember forget (xs , ns' , ns'') (all , all') =
    trans (cong (λ p → (f (fst p , _) , fst p , snd p ,
                        rememberᶜ E (λ y → f (fst p , y)) fold _ (ind-fmapᶜ E remember _)))
                (remember-forget-invʳ D fold remember forget xs ns' all))
          (cong (bimap id ((xs ,_) ∘ (ns' ,_)))
                (remember-forget-invᶜ E (curry f _) fold remember forget ns'' all'))

  remember-forget-invᶜˢ :
      {I : Set ℓⁱ} (D : ConDs I cbs) {X : I → Set ℓˣ} (f : Algᶜˢ D X)
      {N : I → Set ℓ} (fold : ∀ {i} → N i → X i) {N' : Σ[ i ∈ I ] X i × ⊤ → Set ℓ'}
      (remember : ∀ {i} (n : N i) → N' (i , fold n , tt))
      (forget : ∀ {is} → N' is → N (fst is))
    → ∀ {i x} (ns' : ⟦ ⌊ algODᶜˢ D f ⌋ᶜˢ ⟧ᶜˢ N' (i , x , tt))
    → Allᶜˢ ⌊ algODᶜˢ D f ⌋ᶜˢ (λ is n' → let (i' , x' , _) = is in
          (fold (forget n') , remember (forget n'))
        ≡ ((x' , n') ⦂ Σ[ x'' ∈ X i' ] N' (i' , x'' , tt))) ns' ℓ''
    → (f (fmapᶜˢ D fold (eraseᶜˢ ⌈ algODᶜˢ D f ⌉ᶜˢ (fmapᶜˢ ⌊ algODᶜˢ D f ⌋ᶜˢ forget ns'))) ,
      rememberᶜˢ {ℓ'' = ℓ′} D f fold
        (eraseᶜˢ ⌈ algODᶜˢ D f ⌉ᶜˢ (fmapᶜˢ ⌊ algODᶜˢ D f ⌋ᶜˢ forget ns'))
          (ind-fmapᶜˢ D remember
            (eraseᶜˢ ⌈ algODᶜˢ D f ⌉ᶜˢ (fmapᶜˢ ⌊ algODᶜˢ D f ⌋ᶜˢ forget ns'))))
    ≡ ((x , ns') ⦂ Σ[ x' ∈ X i ] (⟦ ⌊ algODᶜˢ D f ⌋ᶜˢ ⟧ᶜˢ N' (i , x' , tt)))
  remember-forget-invᶜˢ (D ∷ Ds) f fold remember forget (inl ns') all =
    cong (bimap id inl)
        (remember-forget-invᶜ  D  (f ∘ inl) fold remember forget ns' all)
  remember-forget-invᶜˢ (D ∷ Ds) f fold remember forget (inr ns') all =
    cong (bimap id inr)
        (remember-forget-invᶜˢ Ds (f ∘ inr) fold remember forget ns' all)

  remember-forget-inv-alg :
    ∀ {D N} (C : DataC D N) {ℓf}
      (alg : Algebrasᵗ D ℓf) (fold : FoldsTᵗ C alg) (foldC : AlgebrasCᵗ C alg fold)
    → ∀ {N'} (C' : DataC ⌊ algOD D alg ⌋ᵈ N')
    → (remember : IndsTᵗ C (remember-alg C alg fold foldC C'))
    → IndAlgebrasCᵗ C (remember-alg C alg fold foldC C') remember
    → (forget : FoldsTᵗ C' (forget-alg ⌈ algOD D alg ⌉ᵈ (DataC.toN C)))
    → AlgebrasCᵗ C' (forget-alg ⌈ algOD D alg ⌉ᵈ (DataC.toN C)) forget
    → IndAlgebrasᵗ C' _
  remember-forget-inv-alg {D} C alg fold foldC {N'} C'
    remember rememberC forget forgetC $$ ℓs $$ ps =
    let alg'      = λ {is} → Algebra.apply (alg $$ ℓs $$ ps) {is}
        fold'     = λ {is} → (fold     $$ ℓs $$ ps) {is}
        remember' = λ {is} → (remember $$ ℓs $$ ps) {is}
        forget'   = λ {is} → (forget   $$ ℓs $$ ps) {is} in record
    { Carrier = λ i n' → let (is , x , _) = i in
        (fold' (forget' n') , remember' (forget' n')) ≡ (x , n')
    ; apply = λ ns' all → let Dᶜˢ = PDataD.applyP (DataD.applyL D ℓs) ps in
        begin
          (let n = forget' (DataC.toN C' ns') in fold' n , remember' n)
            ≡⟨ cong (λ n → fold' n , remember' n) (forgetC ns') ⟩
          let ns = eraseᵈ ⌈ algOD D alg ⌉ᵈ (fmapᵈ ⌊ algOD D alg ⌋ᵈ forget' ns')
              n  = DataC.toN C ns in
        (fold' n , remember' n
            ≡⟨ cong (λ m → fold' (DataC.toN C ns) , m) (rememberC _) ⟩
          fold' n ,
          DataC.toN C' (subst (λ x → ⟦ ⌊ algOD D alg ⌋ᵈ ⟧ᵈ (N' ℓs ps) (_ , x , tt))
                              (sym (foldC _))
                              (rememberᶜˢ Dᶜˢ alg' fold' _ (ind-fmapᵈ D remember' ns)))
            ≡⟨ pair-subst-lemma (DataC.toN C') (sym (foldC _)) ⟩
          alg' (fmapᵈ D fold' ns) ,
          DataC.toN C' (rememberᶜˢ Dᶜˢ alg' fold' _ (ind-fmapᵈ D remember' ns))
            ≡⟨ cong (bimap id (DataC.toN C'))
                    (remember-forget-invᶜˢ Dᶜˢ alg' fold' remember' forget' ns' all) ⟩
          (_ , DataC.toN C' ns')
        ∎) } where open ≡-Reasoning
