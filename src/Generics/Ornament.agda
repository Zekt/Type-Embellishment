{-# OPTIONS --safe #-}

module Generics.Ornament where

open import Generics.Prelude
open import Generics.Description

private
  variable
    ℓ ℓⁱ ℓʲ ℓᵃ  : Level
    ℓf ℓg ℓh ℓk : Level → Level
    I : Set ℓⁱ
    J : Set ℓʲ
    A : Set ℓᵃ

data RecO (e : I → J) : RecD I ℓf → RecD J ℓf → Setω where
  ι : ∀ {i j} (eq : e i ≡ j) → RecO e (ι i) (ι j)
  π : {D : A → RecD I ℓf} {E : A → RecD J ℓf}
      (O : (a : A) → RecO e (D a) (E a)) → RecO e (π A D) (π A E)

eraseʳ : {e : I → J} {D : RecD I ℓf} {E : RecD J ℓf} (O : RecO e D E)
         {X : J → Set ℓ} → ⟦ D ⟧ʳ (λ i → X (e i)) → ⟦ E ⟧ʳ X
eraseʳ (ι eq) x  = subst _ eq x
eraseʳ (π  O) xs = λ a → eraseʳ (O a) (xs a)

data ConO (e : I → J) : ConD I ℓf → ConD J ℓg → Setω where
  ι : ∀ {i j} (eq : e i ≡ j) → ConO e (ι i) (ι j)
  ρ : {R : RecD I ℓf} {S : RecD J ℓf} {D : ConD I ℓg} {E : ConD J ℓh}
      (O : RecO e R S) (O' : ConO e D E) → ConO e (ρ R D) (ρ S E)
  σ : {D : A → ConD I ℓf} {E : A → ConD J ℓg}
      (O : (a : A) → ConO e (D a) (E a)) → ConO e (σ A D) (σ A E)
  Δ : {D : A → ConD I ℓf} {E : ConD J ℓg}
      (O : (a : A) → ConO e (D a)  E   ) → ConO e (σ A D)      E
  ∇ : {D : ConD I ℓf} {E : A → ConD J ℓg}
      (a : A)   (O : ConO e  D    (E a)) → ConO e      D  (σ A E)

eraseᶜ : {e : I → J} {D : ConD I ℓf} {E : ConD J ℓg} (O : ConO e D E)
         {X : J → Set ℓ} {i : I} → ⟦ D ⟧ᶜ (λ i' → X (e i')) i → ⟦ E ⟧ᶜ X (e i)
eraseᶜ (ι eq  ) eq'      = trans (sym eq) (cong _ eq')
eraseᶜ (ρ O O') (x , xs) = eraseʳ O x , eraseᶜ O' xs
eraseᶜ (σ   O ) (a , xs) = a , eraseᶜ (O a) xs
eraseᶜ (Δ   O ) (a , xs) =     eraseᶜ (O a) xs
eraseᶜ (∇ a O )      xs  = a , eraseᶜ  O    xs

data ConOs (e : I → J) : ConDs I ℓf → ConDs J ℓg → Setω where
  ∅   : ConOs e ∅        ∅
  _◁_ : {D : ConD I ℓf} {E : ConD J ℓg} {Ds : ConDs I ℓh} {Es : ConDs J ℓk}
        (O : ConO e D E) (Os : ConOs e Ds (E ◁ Es)) → ConOs e (D ◁ Ds) (E ◁ Es)
  ◂_  : {E : ConD J ℓf} {Ds : ConDs I ℓg} {Es : ConDs J ℓh}
                         (Os : ConOs e Ds      Es ) → ConOs e      Ds  (E ◁ Es)

infixr 4 _◁_
infix  4 ◂_

eraseᶜˢ : {e : I → J} {Ds : ConDs I ℓf} {Es : ConDs J ℓg} (Os : ConOs e Ds Es)
          {X : J → Set ℓ} {i : I} → ⟦ Ds ⟧ᶜˢ (λ i' → X (e i')) i → ⟦ Es ⟧ᶜˢ X (e i)
eraseᶜˢ (O ◁ Os) (inl xs) = inl (eraseᶜ  O  xs)
eraseᶜˢ (O ◁ Os) (inr xs) =      eraseᶜˢ Os xs
eraseᶜˢ (  ◂ Os)      xs  = inr (eraseᶜˢ Os xs)

open DataD

record DataO (D E : DataD) : Setω where
  field
    param : ⟦ Param D ⟧ᵗ → ⟦ Param E ⟧ᵗ
    index : (p : ⟦ Param D ⟧ᵗ) → ⟦ Index D p ⟧ᵗ → ⟦ Index E (param p) ⟧ᵗ
    Orn   : (p : ⟦ Param D ⟧ᵗ) → ConOs (index p) (Desc D p) (Desc E (param p))

eraseᵈ : {D E : DataD} (O : DataO D E) (p : ⟦ Param D ⟧ᵗ)
       → let q = DataO.param O p; index = DataO.index O p in
         {X : ⟦ Index E q ⟧ᵗ → Set ℓ} {i : ⟦ Index D p ⟧ᵗ}
       → ⟦ D ⟧ᵈ p (λ i' → X (index i')) i → ⟦ E ⟧ᵈ q X (index i)
eraseᵈ O p = eraseᶜˢ (DataO.Orn O p)

record UPDataO (D E : UPDataD) : Setω where
  field
    levels : UPDataD.Levels D → UPDataD.Levels E
    Orn    : (ℓs : UPDataD.Levels D)
           → DataO (UPDataD.Desc D ℓs) (UPDataD.Desc E (levels ℓs))

eraseᵘᵖᵈ : {D E : UPDataD} (O : UPDataO D E) (ℓs : UPDataD.Levels D)
         → let ℓs' = UPDataO.levels O ℓs
               Dᵐ  = UPDataD.Desc D ℓs
               Eᵐ  = UPDataD.Desc E ℓs'
               Oᵐ  = UPDataO.Orn O ℓs in
           (p : ⟦ Param Dᵐ ⟧ᵗ)
         → let q = DataO.param Oᵐ p; index = DataO.index Oᵐ p in
           {X : ⟦ Index Eᵐ q ⟧ᵗ → Set ℓ} {i : ⟦ Index Dᵐ p ⟧ᵗ}
         → ⟦ D ⟧ᵘᵖᵈ ℓs p (λ i' → X (index i')) i → ⟦ E ⟧ᵘᵖᵈ ℓs' q X (index i)
eraseᵘᵖᵈ O ℓs p = eraseᶜˢ (DataO.Orn (UPDataO.Orn O ℓs) p)