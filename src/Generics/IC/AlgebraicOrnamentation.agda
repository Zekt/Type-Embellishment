{-# OPTIONS --safe #-}

module Generics.IC.AlgebraicOrnamentation where

open import Generics.Prelude
open import Generics.IC.Description
open import Generics.IC.Algebra

module _ {ℓᵖ ℓⁱ} {P : Tel₀ ℓᵖ} {I : Tel ⟦ P ⟧ᵗ⁰ ℓⁱ} {X : ∀ p → Carrier P I p} where

  algOrnConD : {T : Tel ⟦ P ⟧ᵗ⁰ ℓⁱ} (C : ConD P I T) (T' : Tel ⟦ P ⟧ᵗ⁰ ℓⁱ)
               (proj : {p : ⟦ P ⟧ᵗ⁰} → ⟦ T' ⟧ᵗ p → ⟦ T ⟧ᵗ p)
             → ({p : ⟦ P ⟧ᵗ⁰} {i : ⟦ I ⟧ᵗ p} (t' : ⟦ T' ⟧ᵗ p)
                  → ⟦ C ⟧ᶜ p (proj t') (X p) i → X p i)
             → ConD P (snoc I X) T'
  algOrnConD (ι   i  ) T' proj alg = ι λ p t' → i p (proj t') , alg t' refl
  algOrnConD (ρ U i C) T' proj alg =
    let X' p t' = Curriedᵗ U (p , proj t') λ u → X p (i p (proj t') u)
    in  σ X' (ρ (weakenᵗ (λ e → let (p , t' , _) = e in p , proj t') U)
                (λ p t'' u' → let (t' , x') = t'' in _ , uncurryᵗ x' (weakenᵗ-proj u'))
                (algOrnConD C (snoc T' X') (λ t'' → proj (fst t''))
                   (λ t'' xs → let (t' , x') = t'' in alg t' (uncurryᵗ x' , xs))))
  algOrnConD (σ A   C) T' proj alg =
    let A' p t' = A p (proj t')
    in  σ A' (algOrnConD C (snoc T' A')
               (λ e → let (t' , a) = e in proj t' , a)
               (λ e xs → let (t' , a) = e in  alg t' (a , xs)))

  algOrnD : (D : SetD P I) (alg : ∀ {p} → Alg D p (X p)) → SetD P (snoc I X)
  algOrnD  nil        _   = nil
  algOrnD (cons C Cs) alg = cons (algOrnConD C nil id λ _ xs → Alg.apply alg (inl xs))
                                 (algOrnD Cs (algebra λ xs → Alg.apply alg (inr xs)))