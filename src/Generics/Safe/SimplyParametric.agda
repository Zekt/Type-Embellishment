{-# OPTIONS --safe #-}

module Generics.Safe.SimplyParametric where

open import Prelude
open import Generics.Safe.Telescope
open import Generics.Safe.Description

private variable
  cb  : ConB
  cbs : ConBs

SPᵇ : ConB → Set
SPᵇ []            = ⊤
SPᵇ (inl _  ∷ cb) = Bool × SPᵇ cb
SPᵇ (inr rb ∷ cb) = SPᵇ cb

SPᶜ : {I : Set ℓⁱ} (D : ConD I cb) → SPᵇ cb → Set ℓ → Setω
SPᶜ (ι i  ) s X = Liftω ⊤
SPᶜ (σ A D) (false , s) X = (a : A) → SPᶜ (D a) s X
SPᶜ (σ A D) (true  , s) X = Σωω[ _ ∈ (_ ,ℓ A) ≡ω ((_ ,ℓ X) ⦂ω Σℓ[ ℓ' ] Set ℓ') ]
                           ((a : A) → SPᶜ (D a) s X)
SPᶜ (ρ D E) s X = SPᶜ E s X

SPᶜˢ : {I : Set ℓⁱ} (D : ConDs I cbs) → Set ℓ → Setω
SPᶜˢ []       X = Liftω ⊤
SPᶜˢ (D ∷ Ds) X = Σω[ s ∈ _ ] Σωω[ _ ∈ SPᶜ D s X ] SPᶜˢ Ds X

record SPᵖᵈ (D : PDataD) : Setω where
  constructor sp
  field
    {elevel} : Level
    {plevel} : Level
    {Param}  : Tel plevel
    {Index}  : ⟦ Param ⟧ᵗ → Tel (PDataD.ilevel D)
    equation : (PDataD.plevel D      ,ω PDataD.Param D            ,ωω PDataD.Index D) ≡ω
              ((lsuc elevel ⊔ plevel ,ω Set elevel ∷ constω Param ,ωω λ (_ , ps) → Index ps)
                 ⦂ω Σω[ ℓ ∈ Level ] Σωω[ T ∈ Tel ℓ ] (⟦ T ⟧ᵗ → Tel (PDataD.ilevel D)))
    elements : (ps : ⟦ PDataD.Param D ⟧ᵗ)
             → substω₁ (λ (_ ,ω P ,ωω I) →
                          (ps : ⟦ P ⟧ᵗ) → ConDs ⟦ I ps ⟧ᵗ (PDataD.struct D) → Setω)
                       (symω equation) (λ (A , _) Dᶜˢ → SPᶜˢ Dᶜˢ A)
                       ps (PDataD.applyP D ps)

SP : DataD → Setω
SP D = ∀ ℓs → SPᵖᵈ (DataD.applyL D ℓs)
