{-# OPTIONS --safe #-}

module Generics.Safe.SimplyParametric where

open import Prelude
open import Generics.Safe.Telescope
open import Generics.Safe.Description
open import Generics.Safe.Algebra
open import Generics.Safe.Recursion

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

record SP (D : PDataD) : Setω where
  constructor sp
  field
    {elevel} : Level
    {plevel} : Level
    {Param}  : Tel plevel
    {Index}  : ⟦ Param ⟧ᵗ → Tel (PDataD.ilevel D)
    equation : (PDataD.plevel D      ,ω PDataD.Param D            ,ωω PDataD.Index D) ≡ω
              ((lsuc elevel ⊔ plevel ,ω Set elevel ∷ constω Param ,ωω λ ps → Index (snd ps))
                 ⦂ω Σω[ ℓ ∈ Level ] Σωω[ T ∈ Tel ℓ ] (⟦ T ⟧ᵗ → Tel (PDataD.ilevel D)))
    elements : (ps : ⟦ PDataD.Param D ⟧ᵗ)
             → substω₁ (λ (_ ,ω P ,ωω I) →
                          (ps : ⟦ P ⟧ᵗ) → ConDs ⟦ I ps ⟧ᵗ (PDataD.struct D) → Setω)
                       (symω equation) (λ (A , _) Dᶜˢ → SPᶜˢ Dᶜˢ A)
                       ps (PDataD.applyP D ps)

SPᵈ : DataD → Setω
SPᵈ D = ∀ ℓs → SP (DataD.applyL D ℓs)

-- mapSP-param : (D : PDataD) (S : SP D) (X : Set (SP.elevel S))
--             → ⟦ SP.Param S ⟧ᵗ → ⟦ PDataD.Param D ⟧ᵗ
-- mapSP-param record{} (sp refl es) X ps = X , ps

-- mapSP-Carrier : (D : PDataD) (S : SP D) (N : ∀ ps → Carrierᵖᵈ D ps (PDataD.dlevel D))
--                 (X Y : Set (SP.elevel S)) (ps : ⟦ SP.Param S ⟧ᵗ)
--               → Carrierᶜˢ (PDataD.applyP D (mapSP-param D S X ps)) (PDataD.dlevel D)
-- mapSP-Carrier record{} (sp refl es) N X Y ps is = N (Y , ps) is

-- mapSP-algebra :
--     (D : PDataD) (S : SP D) (N : ∀ ps → Carrierᵖᵈ D ps (PDataD.dlevel D))
--     (toN : ∀ {ps} → Algᵖᵈ D (N ps)) (X Y : Set (SP.elevel S)) (ps : ⟦ SP.Param S ⟧ᵗ)
--   → Algᶜˢ (PDataD.applyP D (mapSP-param D S X ps))
--           (mapSP-Carrier D S N X Y ps)
-- mapSP-algebra D@record{} (sp refl es) N toN X Y ps ns = toN {!   !}

-- mapSP : ∀ {D N} → DataC D N → SPᵈ D → FoldP
-- mapSP {D} {N} C S = record
--   { Conv = C
--   ; #levels = DataD.#levels D
--   ; level = id
--   ; Param = λ ℓs → let ℓ = SP.elevel (S ℓs) in
--       [[ _ ∶ SP.Param (S ℓs) ]]
--       [ X ∶ Set ℓ ] [ Y ∶ Set ℓ ] [ _ ∶ (X → Y) ] []
--   ; param = λ {ℓs} (ps , X , _) → mapSP-param (DataD.applyL D ℓs) (S ℓs) X ps
--   ; Carrier = λ ℓs (ps , X , Y , f , _) →
--       mapSP-Carrier (DataD.applyL D ℓs) (S ℓs) (N ℓs) X Y ps
--   ; algebra = λ {ℓs} (ps , X , Y , f , _) →
--       mapSP-algebra (DataD.applyL D ℓs) (S ℓs) (N ℓs) (DataC.toN C) X Y ps }
