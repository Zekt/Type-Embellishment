{-# OPTIONS --safe #-}

open import Prelude

module Generics.Ornament where
open import Generics.Telescope
open import Generics.Description
open import Generics.Algebra
open import Generics.Recursion

private variable
  A : Set ℓ
  m n : ℕ
  rb  rb'  : RecB
  cb  cb'  : ConB
  cbs cbs' : ConBs

module _ {I : Set ℓⁱ} {J : Set ℓʲ} (e : I → J) where

  infixr 5 _∷_
  infix  5 ∺_

  data RecO : RecD I rb → RecD J rb' → Setω where
    ι : ∀ {i j} (eq : e i ≡ j) → RecO (ι i) (ι j)
    π : {D : A → RecD I rb} {E : A → RecD J rb}
        (O : (a : A) → RecO (D a) (E a)) → RecO (π A D) (π A E)

  data ConO : ConD I cb → ConD J cb' → Setω where
    ι : ∀ {i j} (eq : e i ≡ j) → ConO (ι i) (ι j)
    σ : {D : A → ConD I cb} {E : A → ConD J cb'}
        (O : (a : A) → ConO (D a) (E a)) → ConO (σ A D) (σ A E)
    Δ : {D : A → ConD I cb} {E : ConD J cb'}
        (O : (a : A) → ConO (D a)  E   ) → ConO (σ A D)      E
    ∇ : {D : ConD I cb} {E : A → ConD J cb'}
        (a : A)   (O : ConO  D    (E a)) → ConO      D  (σ A E)
    ρ : {R : RecD I rb} {S : RecD J rb} {D : ConD I cb} {E : ConD J cb'}
        (O : RecO R S) (O' : ConO D E) → ConO (ρ R D) (ρ S E)

  data ConOs : ConDs I cbs → ConDs J cbs' → Setω where
    []  : ConOs [] []
    _∷_ : {D : ConD I cb} {E : ConD J cb'}
          {Ds : ConDs I cbs} {Es : ConDs J cbs'}
          (O : ConO D E) (Os : ConOs Ds (E ∷ Es)) → ConOs (D ∷ Ds) (E ∷ Es)
    ∺_  : {E : ConD J cb} {Ds : ConDs I cbs} {Es : ConDs J cbs'}
                         (Os : ConOs Ds      Es ) → ConOs      Ds  (E ∷ Es)

module _ {I : Set ℓⁱ} {J : Set ℓʲ} {e : I → J} where

  eraseʳ : {D : RecD I rb} {E : RecD J rb} (O : RecO e D E)
           {X : J → Set ℓ} → ⟦ D ⟧ʳ (X ∘ e) → ⟦ E ⟧ʳ X
  eraseʳ (ι eq) x  = subst _ eq x
  eraseʳ (π  O) xs = λ a → eraseʳ (O a) (xs a)

  eraseᶜ : {D : ConD I cb} {E : ConD J cb'} (O : ConO e D E)
           {X : J → Set ℓˣ} {i : I} → ⟦ D ⟧ᶜ (X ∘ e) i → ⟦ E ⟧ᶜ X (e i)
  eraseᶜ (ι eq  ) eq'      = trans (sym eq) (cong _ eq')
  eraseᶜ (σ   O ) (a , xs) = a , eraseᶜ (O a) xs
  eraseᶜ (Δ   O ) (a , xs) =     eraseᶜ (O a) xs
  eraseᶜ (∇ a O )      xs  = a , eraseᶜ  O    xs
  eraseᶜ (ρ O O') (x , xs) = eraseʳ O x , eraseᶜ O' xs

  eraseᶜˢ : {Ds : ConDs I cbs} {Es : ConDs J cbs'} (Os : ConOs e Ds Es)
            {X : J → Set ℓˣ} {i : I} → ⟦ Ds ⟧ᶜˢ (X ∘ e) i → ⟦ Es ⟧ᶜˢ X (e i)
  eraseᶜˢ (O ∷ Os) (inl xs) = inl (eraseᶜ  O  xs)
  eraseᶜˢ (O ∷ Os) (inr xs) =      eraseᶜˢ Os xs
  eraseᶜˢ (  ∺ Os)      xs  = inr (eraseᶜˢ Os xs)

record PDataO (D E : PDataD) : Setω where
  field
    param  : ⟦ PDataD.Param D ⟧ᵗ → ⟦ PDataD.Param E ⟧ᵗ
    index  : (ps : ⟦ PDataD.Param D ⟧ᵗ)
           → ⟦ PDataD.Index D ps ⟧ᵗ → ⟦ PDataD.Index E (param ps) ⟧ᵗ
    applyP : (ps : ⟦ PDataD.Param D ⟧ᵗ)
           → ConOs (index ps) (PDataD.applyP D ps) (PDataD.applyP E (param ps))

record DataO (D E : DataD) : Setω where
  field
    level  : DataD.Levels D → DataD.Levels E
    applyL : (ℓs : DataD.Levels D)
           → PDataO (DataD.applyL D ℓs) (DataD.applyL E (level ℓs))

eraseᵖᵈ : {D E : PDataD} (O : PDataO D E) {ps : ⟦ PDataD.Param D ⟧ᵗ}
        → let qs = PDataO.param O ps; index = PDataO.index O ps in
          {X : ⟦ PDataD.Index E qs ⟧ᵗ → Set ℓ} {i : ⟦ PDataD.Index D ps ⟧ᵗ}
        → ⟦ D ⟧ᵖᵈ (X ∘ index) i → ⟦ E ⟧ᵖᵈ X (index i)
eraseᵖᵈ O {ps} = eraseᶜˢ (PDataO.applyP O ps)

eraseᵈ : {D E : DataD} (O : DataO D E) {ℓs : DataD.Levels D}
       → let Dᵖ = DataD.applyL D ℓs
             Eᵖ = DataD.applyL E (DataO.level O ℓs)
             Oᵖ = DataO.applyL O ℓs in
         {ps : ⟦ PDataD.Param Dᵖ ⟧ᵗ}
       → let qs = PDataO.param Oᵖ ps; index = PDataO.index Oᵖ ps in
         {X : ⟦ PDataD.Index Eᵖ qs ⟧ᵗ → Set ℓ} {is : ⟦ PDataD.Index Dᵖ ps ⟧ᵗ}
       → ⟦ D ⟧ᵈ (X ∘ index) is → ⟦ E ⟧ᵈ X (index is)
eraseᵈ O {ℓs} = eraseᵖᵈ (DataO.applyL O ℓs)

forget : ∀ {D M} → DataC D M → ∀ {E N} → DataC E N → DataO D E → FoldP
forget {D} DC {N = N} EC O = record
  { Conv    = DC
  ; #levels = DataD.#levels D
  ; level   = id
  ; Param   = λ ℓs → PDataD.Param (DataD.applyL D ℓs)
  ; param   = id
  ; Carrier = λ ℓs ps is → let Oᵖ = DataO.applyL O ℓs in
      N (DataO.level O ℓs) (PDataO.param Oᵖ ps) (PDataO.index Oᵖ ps is)
  ; algebra = λ _ → DataC.toN EC ∘ eraseᵈ O }
