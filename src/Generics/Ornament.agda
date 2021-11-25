{-# OPTIONS --safe #-}

module Generics.Ornament where

open import Generics.Prelude
open import Generics.Description

open SetD

data RecO {ℓ} {I J : Set ℓ} (e : I → J) : RecD I → RecD J → Set ℓ where
  ι : ∀ {i j} (eq : e i ≡ j) → RecO e (ι i) (ι j)
  π : ∀ {A D E} (O : (a : A) → RecO e (D a) (E a)) → RecO e (π A D) (π A E)
  Δ : ∀ {A D E}  (a : A)  (O : RecO e (D a)  E   ) → RecO e (π A D)      E
  ∇ : ∀ {A D E} (O : (a : A) → RecO e  D    (E a)) → RecO e      D  (π A E)

eraseʳ : ∀ {ℓ} {I J : Set ℓ} {e : I → J} {D E} (O : RecO e D E) {X}
       → ⟦ D ⟧ʳ (λ j → X (e j)) → ⟦ E ⟧ʳ X
eraseʳ (ι eq ) x  = subst _ eq x
eraseʳ (π   O) xs = λ a → eraseʳ (O a) (xs a)
eraseʳ (Δ a O) xs =       eraseʳ  O    (xs a)
eraseʳ (∇   O) xs = λ a → eraseʳ (O a)  xs

data ConO {ℓ} {I J : Set ℓ} (e : I → J) : ConD I → ConD J → Set ℓ where
  ι : ∀ {i j} (eq : e i ≡ j) → ConO e (ι i) (ι j)
  ρ : ∀ {R S D E} (O : RecO e R S) (O' : ConO e D E) → ConO e (ρ R D) (ρ S E)
  σ : ∀ {A   D E} (O : (a : A) → ConO e (D a) (E a)) → ConO e (σ A D) (σ A E)
  Δ : ∀ {A   D E} (O : (a : A) → ConO e (D a)  E   ) → ConO e (σ A D)      E
  ∇ : ∀ {A   D E}  (a : A)  (O : ConO e  D    (E a)) → ConO e      D  (σ A E)

eraseᶜ : ∀ {ℓ} {I J : Set ℓ} {e : I → J} {D E} (O : ConO e D E)
         {i : I} {X} → ⟦ D ⟧ᶜ (λ j → X (e j)) i → ⟦ E ⟧ᶜ X (e i)
eraseᶜ (ι eq  ) eq'      = trans (sym eq) (cong _ eq')
eraseᶜ (ρ O O') (x , xs) = eraseʳ O x , eraseᶜ O' xs
eraseᶜ (σ   O ) (a , xs) = a , eraseᶜ (O a) xs
eraseᶜ (Δ   O ) (a , xs) =     eraseᶜ (O a) xs
eraseᶜ (∇ a O )      xs  = a , eraseᶜ  O    xs

data ConOs {ℓ} {I J : Set ℓ} (e : I → J) : ConDs I → ConDs J → Set ℓ where
  ∅   : ConOs e ∅        ∅
  _◁_ : ∀ {D E Ds Es} (O : ConO e D E) (Os : ConOs e Ds (E ◁ Es))
      → ConOs e (D ◁ Ds) (E ◁ Es)
  ◂_  : ∀ {  E Ds Es}                  (Os : ConOs e Ds      Es )
      → ConOs e      Ds  (E ◁ Es)

infixr 4 _◁_
infix  4 ◂_

eraseᶜˢ : ∀ {ℓ} {I J : Set ℓ} {e : I → J} {Ds Es} (Os : ConOs e Ds Es)
          {i : I} {X} → ⟦ Ds ⟧ᶜˢ (λ j → X (e j)) i → ⟦ Es ⟧ᶜˢ X (e i)
eraseᶜˢ (O ◁ Os) (inl xs) = inl (eraseᶜ  O  xs)
eraseᶜˢ (O ◁ Os) (inr xs) =      eraseᶜˢ Os xs
eraseᶜˢ (  ◂ Os)      xs  = inr (eraseᶜˢ Os xs)

record SetO {ℓᵖ ℓⁱ} (D E : SetD {ℓᵖ} {ℓⁱ}) : Set (lsuc (ℓᵖ ⊔ ℓⁱ)) where
  field
    param : ⟦ Param D ⟧ᵗ → ⟦ Param E ⟧ᵗ
    index : (p : ⟦ Param D ⟧ᵗ) → ⟦ Index D p ⟧ᵗ → ⟦ Index E (param p) ⟧ᵗ
    Orn   : (p : ⟦ Param D ⟧ᵗ) → ConOs (index p) (Desc D p) (Desc E (param p))

eraseˢ : ∀ {ℓᵖ ℓⁱ} {D E : SetD {ℓᵖ} {ℓⁱ}} (O : SetO D E)
         {p : ⟦ SetD.Param D ⟧ᵗ} {i : ⟦ SetD.Index D p ⟧ᵗ} {X}
       → ⟦ D ⟧ˢ (λ j → X (SetO.index O p j)) i
       → ⟦ E ⟧ˢ X (SetO.index O p i)
eraseˢ O {p} = eraseᶜˢ (SetO.Orn O p)
