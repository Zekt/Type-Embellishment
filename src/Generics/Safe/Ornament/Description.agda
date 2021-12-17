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

mutual

  data TelOD : Tel ℓ → Level → Setω where
    ε : {U : Tel ℓ} → TelOD U ℓ
    ▷ : {U : Tel ℓ''} (OD : TelOD U ℓ)
      → (⟦ ⌊ OD ⌋ᵗ ⟧ᵗ → Set ℓ') → TelOD U (ℓ ⊔ ℓ')
    κ : {A : Set ℓ} {U : A → Tel ℓ''}
      → (OD : ∀ a → TelOD (U a) ℓ') → TelOD (A ∷ U) (ℓ ⊔ ℓ')
    Δ : (A : Set ℓ) {U : Tel ℓ''}
      → (OD : A → TelOD U ℓ') → TelOD U (ℓ ⊔ ℓ')
    ∇ : (a : A) {U : A → Tel ℓ''}
      → (OD : TelOD (U a) ℓ') → TelOD (A ∷ U) ℓ'

  ⌊_⌋ᵗ : {U : Tel ℓ'} → TelOD U ℓ → Tel ℓ
  ⌊ ε {U = U} ⌋ᵗ = U
  ⌊ ▷ OD A    ⌋ᵗ = snocᵗ ⌊ OD ⌋ᵗ A
  ⌊ κ   OD    ⌋ᵗ = _ ∷ λ a → ⌊ OD a ⌋ᵗ
  ⌊ Δ A OD    ⌋ᵗ = A ∷ λ a → ⌊ OD a ⌋ᵗ
  ⌊ ∇ a OD    ⌋ᵗ = ⌊ OD ⌋ᵗ

⌈_⌉ᵗ : {U : Tel ℓ'} (OD : TelOD U ℓ) → TelO ⌊ OD ⌋ᵗ U
⌈ ε      ⌉ᵗ = ε
⌈ ▷ OD A ⌉ᵗ = ▷ ⌈ OD ⌉ᵗ
⌈ κ   OD ⌉ᵗ = κ λ a → ⌈ OD a ⌉ᵗ
⌈ Δ A OD ⌉ᵗ = Δ λ a → ⌈ OD a ⌉ᵗ
⌈ ∇ a OD ⌉ᵗ = ∇ a ⌈ OD ⌉ᵗ

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
    ParamOD : TelOD (PDataD.Param E) plevel
    IndexOD : (p : ⟦ ⌊ ParamOD ⌋ᵗ ⟧ᵗ)
            → TelOD (PDataD.Index E (eraseᵗ ⌈ ParamOD ⌉ᵗ p)) ilevel
    applyP  : (p : ⟦ ⌊ ParamOD ⌋ᵗ ⟧ᵗ)
            → ConODs ⟦ ⌊ IndexOD p ⌋ᵗ ⟧ᵗ (eraseᵗ ⌈ IndexOD p ⌉ᵗ)
                (PDataD.applyP E (eraseᵗ ⌈ ParamOD ⌉ᵗ p)) struct

record DataOD (E : DataD) : Setω where
  field
    #levels : ℕ
    LevelO  : #O Level #levels (DataD.#levels E)
  Levels : Set
  Levels = Level ^ #levels
  field
    applyL : (ℓs : Levels) → PDataOD (DataD.applyL E (erase# LevelO ℓs))

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
  ; Param  = ⌊ PDataOD.ParamOD OD ⌋ᵗ
  ; Index  = λ p → ⌊ PDataOD.IndexOD OD p ⌋ᵗ
  ; applyP = λ p → ⌊ PDataOD.applyP OD p ⌋ᶜˢ
  }

⌈_⌉ᵖᵈ : ∀ {E} (OD : PDataOD E) → PDataO ⌊ OD ⌋ᵖᵈ E
⌈ OD ⌉ᵖᵈ = record
  { ParamO = ⌈ PDataOD.ParamOD OD ⌉ᵗ
  ; IndexO = λ p → ⌈ PDataOD.IndexOD OD p ⌉ᵗ
  ; applyP = λ p → ⌈ PDataOD.applyP OD p ⌉ᶜˢ
  }

⌊_⌋ᵈ : ∀ {E} → DataOD E → DataD
⌊ OD ⌋ᵈ = record
  { #levels = DataOD.#levels OD
  ; applyL = λ ℓs → ⌊ DataOD.applyL OD ℓs ⌋ᵖᵈ }

⌈_⌉ᵈ : ∀ {E} (OD : DataOD E) → DataO ⌊ OD ⌋ᵈ E
⌈ OD ⌉ᵈ = record
  { LevelO = DataOD.LevelO OD
  ; applyL = λ ℓs → ⌈ DataOD.applyL OD ℓs ⌉ᵖᵈ }

module ODFunctor {I : Set ℓⁱ} {J : Set ℓʲ} {e : I → J} {K : Set ℓᵏ} where

  module _ (f : I → K) (e' : K → J) (coh : ∀ i → e' (f i) ≡ e i) where

    imapODʳ : {D : RecD J rb} → RecOD I e D → RecOD K e' D
    imapODʳ (ι i eq) = ι (f i) (trans (coh i) eq)
    imapODʳ (π OD  ) = π λ a → imapODʳ (OD a)

    imapODᶜ : {D : ConD J cb} → ConOD I e D cb' → ConOD K e' D cb'
    imapODᶜ (ι i eq  ) = ι (f i) (trans (coh i) eq)
    imapODᶜ (σ    OD ) = σ λ a → imapODᶜ (OD a)
    imapODᶜ (Δ A  OD ) = Δ A λ a → imapODᶜ (OD a)
    imapODᶜ (∇ a  OD ) = ∇ a (imapODᶜ OD)
    imapODᶜ (ρ OD OD') = ρ (imapODʳ OD) (imapODᶜ OD')

    imapODᶜˢ : {D : ConDs J cbs} → ConODs I e D cbs' → ConODs K e' D cbs'
    imapODᶜˢ []         = []
    imapODᶜˢ (OD ∷ ODs) = imapODᶜ OD ∷ imapODᶜˢ ODs
    imapODᶜˢ (   ∺ ODs) =            ∺ imapODᶜˢ ODs

  module _ {f : I → K} {e' : K → J} {coh : ∀ i → e' (f i) ≡ e i} where

    imapOD-injʳ : {D : RecD J rb} (OD : RecOD I e D) {X : K → Set ℓˣ}
                → ⟦ ⌊ OD ⌋ʳ ⟧ʳ (X ∘ f) → ⟦ ⌊ imapODʳ f e' coh OD ⌋ʳ ⟧ʳ X
    imapOD-injʳ (ι i eq) x  = x
    imapOD-injʳ (π OD  ) xs = λ a → imapOD-injʳ (OD a) (xs a)

    imapOD-injᶜ : {D : ConD J cb} (OD : ConOD I e D cb') {X : K → Set ℓˣ}
                → ∀ {i} → ⟦ ⌊ OD ⌋ᶜ ⟧ᶜ (X ∘ f) i
                → ⟦ ⌊ imapODᶜ f e' coh OD ⌋ᶜ ⟧ᶜ X (f i)
    imapOD-injᶜ (ι i _   ) eq         = cong f eq
    imapOD-injᶜ (σ    OD ) (a , xs)   = a , imapOD-injᶜ (OD a) xs
    imapOD-injᶜ (Δ A  OD ) (a , xs)   = a , imapOD-injᶜ (OD a) xs
    imapOD-injᶜ (∇ a  OD )      xs    =     imapOD-injᶜ  OD    xs
    imapOD-injᶜ (ρ OD OD') (xs , xs') = imapOD-injʳ OD xs , imapOD-injᶜ OD' xs'

    imapOD-injᶜˢ : {D : ConDs J cbs} (OD : ConODs I e D cbs') {X : K → Set ℓˣ}
                 → ∀ {i} → ⟦ ⌊ OD ⌋ᶜˢ ⟧ᶜˢ (X ∘ f) i
                 → ⟦ ⌊ imapODᶜˢ f e' coh OD ⌋ᶜˢ ⟧ᶜˢ X (f i)
    imapOD-injᶜˢ (OD ∷ ODs) (inl xs) = inl (imapOD-injᶜ  OD  xs)
    imapOD-injᶜˢ (OD ∷ ODs) (inr xs) = inr (imapOD-injᶜˢ ODs xs)
    imapOD-injᶜˢ (   ∺ ODs)      xs  =      imapOD-injᶜˢ ODs xs
