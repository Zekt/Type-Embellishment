{-# OPTIONS --safe #-}

module Generics.Safe.Ornament.Description where

open import Prelude
open import Generics.Safe.Telescope
open import Generics.Safe.Description
open import Generics.Safe.Ornament

private variable
  A : Set ℓ
  n : ℕ
  rb  rb'  : RecB
  cb  cb'  : ConB
  cbs cbs' : ConBs

module _ (I : Set ℓⁱ) {J : Set ℓʲ} (e : I → J) where

  infixr 5 _∷_
  infix  5 ∺_

  data RecOD : RecD J rb → Setω where
    ι : ∀ i {j} (eq : e i ≡ j) → RecOD (ι j)
    π : {E : A → RecD J rb} (OD : (a : A) → RecOD (E a)) → RecOD (π A E)

  data ConOD : ConD J cb → ConB → Setω where
    ι : ∀ i {j} (eq : e i ≡ j) → ConOD (ι j) []
    σ : {A : Set ℓ} {E : A → ConD J cb}
        (OD : (a : A) → ConOD (E a) cb') → ConOD (σ A E) (inl ℓ ∷ cb')
    Δ : (A : Set ℓ) {E : ConD J cb}
        (OD : (a : A) → ConOD E cb') → ConOD E (inl ℓ ∷ cb')
    ∇ : {E : A → ConD J cb} (a : A) (OD : ConOD (E a) cb') → ConOD (σ A E) cb'
    ρ : {S : RecD J rb} {E : ConD J cb}
        (OD : RecOD S) (OD' : ConOD E cb') → ConOD (ρ S E) (inr rb ∷ cb')

  data ConODs : ConDs J cbs → ConBs → Setω where
    []  : ConODs [] []
    _∷_ : {E : ConD J cb} {Es : ConDs J cbs}
          (OD : ConOD E cb') (ODs : ConODs (E ∷ Es) cbs')
        → ConODs (E ∷ Es) (cb' ∷ cbs')
    ∺_  : {E : ConD J cb} {Es : ConDs J cbs}
          (ODs : ConODs Es cbs') → ConODs (E ∷ Es) cbs'

record PDataOD (E : PDataD) : Setω where
  field
    alevel   : Level
    {plevel} : Level
    {ilevel} : Level
    {struct} : ConBs
  dlevel : Level
  dlevel = alevel ⊔ ilevel
  flevel : Level → Level
  flevel ℓ = maxMap max-π struct ⊔ maxMap max-σ struct ⊔
             maxMap (hasRec? ℓ) struct ⊔ hasCon? ilevel struct
  field
    level-pre-fixed-point : flevel dlevel ⊑ dlevel
    Param  : Tel plevel
    param  : ⟦ Param ⟧ᵗ → ⟦ PDataD.Param E ⟧ᵗ
    Index  : ⟦ Param ⟧ᵗ → Tel ilevel
    index  : (ps : ⟦ Param ⟧ᵗ) → ⟦ Index ps ⟧ᵗ → ⟦ PDataD.Index E (param ps) ⟧ᵗ
    applyP : (ps : ⟦ Param ⟧ᵗ)
           → ConODs ⟦ Index ps ⟧ᵗ (index ps) (PDataD.applyP E (param ps)) struct

record DataOD (E : DataD) : Setω where
  field
    #levels : ℕ
  Levels : Set
  Levels = Level ^ #levels
  field
    level  : Levels → DataD.Levels E
    applyL : (ℓs : Levels) → PDataOD (DataD.applyL E (level ℓs))

module _ {I : Set ℓⁱ} {J : Set ℓʲ} {e : I → J} where

  ⌊_⌋ʳ : {E : RecD J rb} → RecOD I e E → RecD I rb
  ⌊ ι i eq ⌋ʳ = ι i
  ⌊ π OD   ⌋ʳ = π _ λ a → ⌊ OD a ⌋ʳ

  ⌈_⌉ʳ : {E : RecD J rb} (OD : RecOD I e E) → RecO e ⌊ OD ⌋ʳ E
  ⌈ ι i eq ⌉ʳ = ι eq
  ⌈ π OD   ⌉ʳ = π λ a → ⌈ OD a ⌉ʳ

  ⌊_⌋ᶜ : {E : ConD J cb} → ConOD I e E cb' → ConD I cb'
  ⌊ ι i eq   ⌋ᶜ = ι i
  ⌊ ρ OD OD' ⌋ᶜ = ρ ⌊ OD ⌋ʳ ⌊ OD' ⌋ᶜ
  ⌊ σ    OD  ⌋ᶜ = σ _ λ a → ⌊ OD a ⌋ᶜ
  ⌊ Δ A  OD  ⌋ᶜ = σ A λ a → ⌊ OD a ⌋ᶜ
  ⌊ ∇ a  OD  ⌋ᶜ = ⌊ OD ⌋ᶜ

  ⌈_⌉ᶜ : {E : ConD J cb} (OD : ConOD I e E cb') → ConO e ⌊ OD ⌋ᶜ E
  ⌈ ι i eq   ⌉ᶜ = ι eq
  ⌈ ρ OD OD' ⌉ᶜ = ρ ⌈ OD ⌉ʳ ⌈ OD' ⌉ᶜ
  ⌈ σ    OD  ⌉ᶜ = σ λ a → ⌈ OD a ⌉ᶜ
  ⌈ Δ A  OD  ⌉ᶜ = Δ λ a → ⌈ OD a ⌉ᶜ
  ⌈ ∇ a  OD  ⌉ᶜ = ∇ a ⌈ OD ⌉ᶜ

  ⌊_⌋ᶜˢ : {Es : ConDs J cbs} → ConODs I e Es cbs' → ConDs I cbs'
  ⌊ []       ⌋ᶜˢ = []
  ⌊ OD ∷ ODs ⌋ᶜˢ = ⌊ OD ⌋ᶜ ∷ ⌊ ODs ⌋ᶜˢ
  ⌊    ∺ ODs ⌋ᶜˢ = ⌊ ODs ⌋ᶜˢ

  ⌈_⌉ᶜˢ : {Es : ConDs J cbs} (ODs : ConODs I e Es cbs') → ConOs e ⌊ ODs ⌋ᶜˢ Es
  ⌈ []       ⌉ᶜˢ = []
  ⌈ OD ∷ ODs ⌉ᶜˢ = ⌈ OD ⌉ᶜ ∷ ⌈ ODs ⌉ᶜˢ
  ⌈    ∺ ODs ⌉ᶜˢ =         ∺ ⌈ ODs ⌉ᶜˢ

⌊_⌋ᵖᵈ : ∀ {E} → PDataOD E → PDataD
⌊ OD ⌋ᵖᵈ = record
  { alevel = PDataOD.alevel OD
  ; level-pre-fixed-point = PDataOD.level-pre-fixed-point OD
  ; Param  = PDataOD.Param OD
  ; Index  = PDataOD.Index OD
  ; applyP = λ ps → ⌊ PDataOD.applyP OD ps ⌋ᶜˢ }

⌈_⌉ᵖᵈ : ∀ {E} (OD : PDataOD E) → PDataO ⌊ OD ⌋ᵖᵈ E
⌈ OD ⌉ᵖᵈ = record
  { param  = PDataOD.param OD
  ; index  = PDataOD.index OD
  ; applyP = λ ps → ⌈ PDataOD.applyP OD ps ⌉ᶜˢ }

⌊_⌋ᵈ : ∀ {E} → DataOD E → DataD
⌊ OD ⌋ᵈ = record
  { #levels = DataOD.#levels OD
  ; applyL = λ ℓs → ⌊ DataOD.applyL OD ℓs ⌋ᵖᵈ }

⌈_⌉ᵈ : ∀ {E} (OD : DataOD E) → DataO ⌊ OD ⌋ᵈ E
⌈ OD ⌉ᵈ = record
  { level  = DataOD.level OD
  ; applyL = λ ℓs → ⌈ DataOD.applyL OD ℓs ⌉ᵖᵈ }

module ODFunctor {I : Set ℓⁱ} {J : Set ℓʲ} {e : I → J} {K : Set ℓᵏ} where

  module _ (f : K → I) (f' : I → K) (inv : ∀ i → f (f' i) ≡ i) where

    imapODʳ : {D : RecD J rb} → RecOD I e D → RecOD K (e ∘ f) D
    imapODʳ (ι i eq) = ι (f' i) (trans (cong e (inv i)) eq)
    imapODʳ (π OD  ) = π λ a → imapODʳ (OD a)

    imapODᶜ : {D : ConD J cb} → ConOD I e D cb' → ConOD K (e ∘ f) D cb'
    imapODᶜ (ι i eq  ) = ι (f' i) (trans (cong e (inv i)) eq)
    imapODᶜ (σ    OD ) = σ λ a → imapODᶜ (OD a)
    imapODᶜ (Δ A  OD ) = Δ A λ a → imapODᶜ (OD a)
    imapODᶜ (∇ a  OD ) = ∇ a (imapODᶜ OD)
    imapODᶜ (ρ OD OD') = ρ (imapODʳ OD) (imapODᶜ OD')

    imapODᶜˢ : {D : ConDs J cbs} → ConODs I e D cbs' → ConODs K (e ∘ f) D cbs'
    imapODᶜˢ []         = []
    imapODᶜˢ (OD ∷ ODs) = imapODᶜ OD ∷ imapODᶜˢ ODs
    imapODᶜˢ (   ∺ ODs) =            ∺ imapODᶜˢ ODs

  module _ {f : K → I} {f' : I → K} {inv : ∀ i → f (f' i) ≡ i} where

    imapOD-injʳ : {D : RecD J rb} (OD : RecOD I e D) {X : K → Set ℓˣ}
                → ⟦ ⌊ OD ⌋ʳ ⟧ʳ (X ∘ f') → ⟦ ⌊ imapODʳ f f' inv OD ⌋ʳ ⟧ʳ X
    imapOD-injʳ (ι i eq) x  = x
    imapOD-injʳ (π OD  ) xs = λ a → imapOD-injʳ (OD a) (xs a)

    imapOD-injᶜ : {D : ConD J cb} (OD : ConOD I e D cb') {X : K → Set ℓˣ}
                → ∀ {i} → ⟦ ⌊ OD ⌋ᶜ ⟧ᶜ (X ∘ f') i
                → ⟦ ⌊ imapODᶜ f f' inv OD ⌋ᶜ ⟧ᶜ X (f' i)
    imapOD-injᶜ (ι i _   ) eq         = cong f' eq
    imapOD-injᶜ (σ    OD ) (a , xs)   = a , imapOD-injᶜ (OD a) xs
    imapOD-injᶜ (Δ A  OD ) (a , xs)   = a , imapOD-injᶜ (OD a) xs
    imapOD-injᶜ (∇ a  OD )      xs    =     imapOD-injᶜ  OD    xs
    imapOD-injᶜ (ρ OD OD') (xs , xs') = imapOD-injʳ OD xs , imapOD-injᶜ OD' xs'

    imapOD-injᶜˢ : {D : ConDs J cbs} (OD : ConODs I e D cbs') {X : K → Set ℓˣ}
                 → ∀ {i} → ⟦ ⌊ OD ⌋ᶜˢ ⟧ᶜˢ (X ∘ f') i
                 → ⟦ ⌊ imapODᶜˢ f f' inv OD ⌋ᶜˢ ⟧ᶜˢ X (f' i)
    imapOD-injᶜˢ (OD ∷ ODs) (inl xs) = inl (imapOD-injᶜ  OD  xs)
    imapOD-injᶜˢ (OD ∷ ODs) (inr xs) = inr (imapOD-injᶜˢ ODs xs)
    imapOD-injᶜˢ (   ∺ ODs)      xs  =      imapOD-injᶜˢ ODs xs

    imapOD-projʳ : {D : RecD J rb} (OD : RecOD I e D) {X : I → Set ℓˣ}
                 → ⟦ ⌊ imapODʳ f f' inv OD ⌋ʳ ⟧ʳ (X ∘ f) → ⟦ ⌊ OD ⌋ʳ ⟧ʳ X
    imapOD-projʳ (ι i eq) {X} x  = subst X (inv i) x
    imapOD-projʳ (π OD  )     xs = λ a → imapOD-projʳ (OD a) (xs a)

    imapOD-projᶜ : {D : ConD J cb} (OD : ConOD I e D cb') {X : I → Set ℓˣ}
                 → ∀ {k} → ⟦ ⌊ imapODᶜ f f' inv OD ⌋ᶜ ⟧ᶜ (X ∘ f) k
                 → ⟦ ⌊ OD ⌋ᶜ ⟧ᶜ X (f k)
    imapOD-projᶜ (ι i _   ) eq = trans (sym (inv i)) (cong f eq)
    imapOD-projᶜ (σ    OD ) (a , xs)   = a , imapOD-projᶜ (OD a) xs
    imapOD-projᶜ (Δ A  OD ) (a , xs)   = a , imapOD-projᶜ (OD a) xs
    imapOD-projᶜ (∇ a  OD )      xs    =     imapOD-projᶜ  OD    xs
    imapOD-projᶜ (ρ OD OD') (xs , xs') = imapOD-projʳ OD xs , imapOD-projᶜ OD' xs'

    imapOD-projᶜˢ : {D : ConDs J cbs} (OD : ConODs I e D cbs') {X : I → Set ℓˣ}
                  → ∀ {k} → ⟦ ⌊ imapODᶜˢ f f' inv OD ⌋ᶜˢ ⟧ᶜˢ (X ∘ f) k
                  → ⟦ ⌊ OD ⌋ᶜˢ ⟧ᶜˢ X (f k)
    imapOD-projᶜˢ (OD ∷ ODs) (inl xs) = inl (imapOD-projᶜ  OD  xs)
    imapOD-projᶜˢ (OD ∷ ODs) (inr xs) = inr (imapOD-projᶜˢ ODs xs)
    imapOD-projᶜˢ (   ∺ ODs)      xs  =      imapOD-projᶜˢ ODs xs
