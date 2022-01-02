{-# OPTIONS --safe #-}

module Generics.Safe.Ornament where

open import Prelude
open import Generics.Safe.Telescope; open ∀ℓ; open ∀ᵐᵗ
open import Generics.Safe.Description
open import Generics.Safe.Algebra
open import Generics.Safe.Recursion

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
    param  : ⟦ PDataD.Param D ⟧ᵐᵗ → ⟦ PDataD.Param E ⟧ᵐᵗ
    index  : (ps : ⟦ PDataD.Param D ⟧ᵐᵗ)
           → ⟦ PDataD.Index D ps ⟧ᵐᵗ → ⟦ PDataD.Index E (param ps) ⟧ᵐᵗ
    applyP : (ps : ⟦ PDataD.Param D ⟧ᵐᵗ)
           → ConOs (index ps) (PDataD.applyP D ps) (PDataD.applyP E (param ps))

record DataO (D E : DataD) : Setω where
  field
    level  : DataD.Levels D → DataD.Levels E
    applyL : (ℓs : DataD.Levels D)
           → PDataO (DataD.applyL D ℓs) (DataD.applyL E (level ℓs))

eraseᵖᵈ : {D E : PDataD} (O : PDataO D E) {ps : ⟦ PDataD.Param D ⟧ᵐᵗ}
        → let qs = PDataO.param O ps; index = PDataO.index O ps in
          {X : ⟦ PDataD.Index E qs ⟧ᵐᵗ → Set ℓ} {i : ⟦ PDataD.Index D ps ⟧ᵐᵗ}
        → ⟦ D ⟧ᵖᵈ (X ∘ index) i → ⟦ E ⟧ᵖᵈ X (index i)
eraseᵖᵈ O {ps} = eraseᶜˢ (PDataO.applyP O ps)

eraseᵈ : {D E : DataD} (O : DataO D E) {ℓs : DataD.Levels D}
       → let Dᵖ = DataD.applyL D ℓs
             Eᵖ = DataD.applyL E (DataO.level O ℓs)
             Oᵖ = DataO.applyL O ℓs in
         {ps : ⟦ PDataD.Param Dᵖ ⟧ᵐᵗ}
       → let qs = PDataO.param Oᵖ ps; index = PDataO.index Oᵖ ps in
         {X : ⟦ PDataD.Index Eᵖ qs ⟧ᵐᵗ → Set ℓ} {is : ⟦ PDataD.Index Dᵖ ps ⟧ᵐᵗ}
       → ⟦ D ⟧ᵈ (X ∘ index) is → ⟦ E ⟧ᵈ X (index is)
eraseᵈ O {ℓs} = eraseᵖᵈ (DataO.applyL O ℓs)

forget-alg : ∀ {D E} (O : DataO D E) {ℓf} {X : Carriers E ℓf} → Algs E X → Algebrasᵗ D _
forget-alg O {_} {X} f $$ ℓs $$ ps = record
  { Carrier = λ is → let Oᵖ = DataO.applyL O ℓs
                     in  X (DataO.level  O  ℓs   )
                           (PDataO.param Oᵖ ps   )
                           (PDataO.index Oᵖ ps is)
  ; apply = f ∘ eraseᵈ O }
