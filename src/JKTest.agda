{-# OPTIONS --safe #-}

open import Prelude
open import Generics.Safe.Telescope
open import Generics.Safe.Description
open import Generics.Safe.Description.FixedPoint
open import Generics.Safe.Algebra
open import Generics.Safe.Ornament
open import Generics.Safe.Ornament.Description
open import Generics.Safe.Ornament.Algebraic
open import Generics.Safe.Ornament.Algebraic.Properties
open import Generics.Safe.Ornament.Promotion
open import Generics.Safe.Recursion
open import Generics.Safe.RecursionScheme

-- META
NatD : DataD
NatD = record
  { #levels = 0
  ; applyL  = λ _ → record
      { alevel = lzero
      ; level-pre-fixed-point = refl
      ; Param  = []
      ; Index  = λ _ → []
      ; applyP = λ _ → ι tt
                     ∷ ρ (ι tt) (ι tt)
                     ∷ [] } }

-- META
ℕ-wrapper : DataT NatD
ℕ-wrapper _ _ _ = ℕ

-- META
NatC : DataC NatD ℕ-wrapper
NatC = record
  { toN   = λ { (inl           refl  ) → zero
              ; (inr (inl (n , refl))) → suc n }
  ; fromN = λ {  zero   → inl           refl
              ; (suc n) → inr (inl (n , refl)) }
  ; fromN-toN = λ { (inl           refl  ) → refl
                  ; (inr (inl (n , refl))) → refl }
  ; toN-fromN = λ {  zero   → refl
                  ; (suc n) → refl } }

-- USER (specialising a generic library component)
foldℕ-alg : ∀ ℓs ps ℓ (X : Set ℓ) → X → (X → X) → Algebraᵈ NatD ℓs ps ℓ
-- foldℕ-alg : {! ∀ ℓs ps ℓ → FoldAlgTᵈ NatD ℓs ps ℓ !}
foldℕ-alg = fold-algᵈ NatD

-- META
foldℕ-wrapper : ∀ ℓs ps ℓ (X : Set ℓ) (z : X) (s : X → X)
              → FoldT NatC ℓs ps (foldℕ-alg ℓs ps ℓ X z s)
foldℕ : {ℓ : Level} (X : Set ℓ) (z : X) (s : X → X) → ℕ → X
-- foldℕ : {- optimised version of -} {! ∀ {ℓs ps ℓ} (X : Set ℓ) (z : X) (s : X → X) → FoldT NatC (foldℕ-alg X z s) !}

-- META
foldℕ-wrapper _ _ _ X z s n = foldℕ X z s n
foldℕ X z s  zero   = z
foldℕ X z s (suc n) = s (foldℕ X z s n)
-- foldℕ X z s  zero   = {! fold-base NatC (fold-algᵈ NatD X z s) (foldℕ-wrapper X z s)  zero   !}
-- foldℕ X z s (suc n) = {! fold-base NatC (fold-algᵈ NatD X z s) (foldℕ-wrapper X z s) (suc n) !}

-- USER (changing the form of the fold)
-- foldℕ-wrapper ℓs ps ℓ X z s n = foldℕ s z n
-- foldℕ : ∀ {ℓ} {X : Set ℓ} → (X → X) → X → ℕ → X
-- foldℕ s z  zero   = z
-- foldℕ s z (suc n) = s (foldℕ s z n)

-- META
foldℕ-is-fold : ∀ ℓs ps ℓ (X : Set ℓ) (z : X) (s : X → X)
              → AlgC NatC (foldℕ-alg ℓs ps ℓ X z s) (foldℕ-wrapper ℓs ps ℓ X z s)
foldℕ-is-fold ℓs ps ℓ X z s (inl           refl  ) = refl
foldℕ-is-fold ℓs ps ℓ X z s (inr (inl (_ , refl))) = refl

-- USER (for now; will be a specialisation of a generic library component)
indℕ-alg : (P : ℕ → Set) → P zero → (∀ n → P n → P (suc n)) → IndAlgebraᵈ NatC tt tt _
indℕ-alg P z s = record
  { Carrier = λ _ → P
  ; apply = λ { (inl           refl  ) _        → z
              ; (inr (inl (n , refl))) (pn , _) → s n pn } }

-- META
indℕ : (P : ℕ → Set) → P zero → (∀ n → P n → P (suc n)) → ∀ n → P n
indℕ P z s  zero   = z
indℕ P z s (suc n) = s n (indℕ P z s n)
-- indℕ P z s  zero   = {! ind-base NatC (indℕ-alg P z s) (indℕ P z s)  zero   !}
-- indℕ P z s (suc n) = {! ind-base NatC (indℕ-alg P z s) (indℕ P z s) (suc n) !}

-- META
indℕ-is-ind : (P : ℕ → Set) (z : P zero) (s : ∀ n → P n → P (suc n))
            → IndAlgC NatC (indℕ-alg P z s) (indℕ P z s)
indℕ-is-ind P z s (inl           refl  ) = refl
indℕ-is-ind P z s (inr (inl (n , refl))) = refl

ListOD : DataOD NatD
ListOD = record
  { #levels = 1
  ; LevelO  = Δ (λ _ → ε)
  ; applyL  = λ ℓs → let (ℓ , _) = ℓs in record
      { alevel  = ℓ; level-pre-fixed-point = refl
      ; ParamOD = Δ (Set ℓ) λ _ → ε
      ; IndexOD = λ _ → ε
      ; applyP  = λ ps → let (A , _) = ps
                         in (ι tt refl)
                        ∷ ∺ (Δ A λ _ → ρ (ι tt refl) (ι tt refl))
                        ∷ ∺ [] } }

ListD : DataD
ListD = ⌊ ListOD ⌋ᵈ

VecOD : DataOD ListD
VecOD = algODᵈ ListD (ornAlg ⌈ ListOD ⌉ᵈ NatC)

VecD : DataD
VecD = ⌊ VecOD ⌋ᵈ

ListD' : Set → DataOD ListD
ListD' A = record
  { #levels = 0
  ; LevelO  = ∇ lzero ε
  ; applyL  = λ _ → record
      { alevel  = lzero
      ; level-pre-fixed-point = refl
      ; ParamOD = ∇ A ε
      ; IndexOD = λ _ → ε
      ; applyP  = λ _ → (ι tt refl)
                    ∷ ∺ (σ λ _ → ρ (ι tt refl) (ι tt refl))
                    ∷ ∺ [] } }

data W {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  sup : (a : A) → (B a → W A B) → W A B

WD : DataD
WD = record
  { #levels = 2
  ; applyL  = λ ℓs → let (ℓ , ℓ' , _) = ℓs in record
      { alevel = ℓ ⊔ ℓ'; level-pre-fixed-point = refl
      ; Param  = [ A ∶ Set ℓ ] [ _ ∶ (A → Set ℓ') ] []
      ; Index  = λ _ → []
      ; applyP = λ ps → let (A , B , _) = ps
                       in (σ A λ a → ρ (π (B a) λ _ → ι tt) (ι tt))
                        ∷ [] } }

PointwiseD : DataD
PointwiseD = record
  { #levels = 3
  ; applyL  = λ ℓs → let (ℓᵃ , ℓᵇ , ℓʳ , _) = ℓs in record
      { alevel = ℓᵃ ⊔ ℓᵇ ⊔ ℓʳ
      ; level-pre-fixed-point = refl
      ; Param  = [ A ∶ Set ℓᵃ ] [ B ∶ Set ℓᵇ ] [ _ ∶ (A → B → Set ℓʳ) ] []
      ; Index  = λ p → let (A , B , R , _) = p
                       in [ _ ∶ List A ] [ _ ∶ List B ] []
      ; applyP = λ p → let (A , B , R , _) = p
                       in (ι ([] , [] , tt))
                        ∷ (σ  A       λ a  →
                           σ  B       λ b  →
                           σ (R a b ) λ _  →
                           σ (List A) λ as →
                           σ (List B) λ bs →
                           ρ (ι (as , bs , tt))
                          (ι (a ∷ as , b ∷ bs , tt)))
                        ∷ [] } }

-- mutual

--   data Even : ℕ → Set where
--     zero : Even zero
--     suc  : ∀ {n} → Odd n → Even (suc n)

--   data Odd : ℕ → Set where
--     suc : ∀ {n} → Even n → Odd (suc n)

-- parity : Algᵈ ⌊ SNatOD ⌋ᵈ λ _ _ _ → Bool
-- parity (inl               refl  ) = false
-- parity (inr (inl (_ , b , refl))) = not b

-- PNatOD : DataOD ⌊ SNatOD ⌋ᵈ
-- PNatOD = algODᵈ ⌊ SNatOD ⌋ᵈ (λ _ _ → algebra _ parity)

-- data PNat : ℕ → Bool → Set where
--   zero : PNat zero false
--   suc  : ∀ {n b} → PNat n b → PNat (suc n) (not b)

-- ParityOD : DataOD ⌊ PNatOD ⌋ᵈ
-- ParityOD = record
--   { #levels = 0
--   ; LevelO  = ε
--   ; applyL  = λ _ → record
--       { alevel  = lzero
--       ; level-pre-fixed-point = refl
--       ; ParamOD = ε
--       ; IndexOD = λ _ → ε
--       ; applyP  = λ _ → (ι _ refl)
--                     ∷ ∺ (σ λ n → ∇ false (ρ (ι _ refl) (ι _ refl)))
--                     ∷   (σ λ n → ∇ true  (ρ (ι _ refl) (ι _ refl)))
--                     ∷ ∺ [] } }

-- data Parity : ℕ → Bool → Set where
--   zero : Parity zero false
--   suc₀ : ∀ {n} → Parity n false → Parity (suc n) true
--   suc₁ : ∀ {n} → Parity n true  → Parity (suc n) false

-- Even' Odd' : ℕ → Set
-- Even' n = Parity n false
-- Odd'  n = Parity n true

-- VecD/NatD : SetO VecD NatD
-- VecD/NatD = record
--   { param = λ _ → tt
--   ; index = λ _ _ → tt
--   ; applyP   = λ { (_ , A) → ι refl
--                       ∷ ◂ Δ (λ a → Δ λ n → ρ (ι refl) (ι refl))
--                       ∷ ◂ [] } }

-- ListD : PDataD {_} {lzero}
-- ListD = record
--   { Param = [] ▷ (λ _ → Set)
--   ; Index = λ _ → []
--   ; Desc  = λ { (_ , A) → ι tt
--                         ∷ σ A (λ _ → ρ (ι tt) (ι tt))
--                         ∷ [] } }

-- BinOD : SetOD ListD
-- BinOD = record
--   { Param = []
--   ; param = λ _ → tt , Bool
--   ; Index = λ _ → []
--   ; index = λ _ _ → tt
--   ; applyP   = λ _ → ι tt refl
--               ∷ ◂ ∇ false (ρ (ι tt refl) (ι tt refl))
--               ∷   ∇ true  (ρ (ι tt refl) (ι tt refl))
--               ∷ ◂ [] }

-- VecD' : ⟦ [] ▷ (λ _ → Set) ⟧ᵗ → PDataD {lsuc lzero}
-- VecD' (_ , A) = record
--   { Param = []
--   ; Index = λ _ → [] ▷ (λ _ → ℕ)
--   ; Desc  = λ _ → ι (tt , zero)
--                 ∷ σ A (λ _ → σ ℕ λ n → ρ (ι (tt , n)) (ι (tt , suc n)))
--                 ∷ [] }

-- open import Data.Vec

-- toVec' : {p : ⟦ [] ▷ (λ _ → Set) ⟧ᵗ} {i : ⟦ [] ▷ (λ _ → ℕ) ⟧ᵗ}
--        → ⟦ VecD' p ⟧ˢ (Vec (snd p) ∘ snd) i → Vec (snd p) (snd i)
-- toVec' (inl                    refl  ) = []
-- toVec' (inr (inl (a , _ , as , refl))) = a ∷ as

-- fromVec' : {p : ⟦ [] ▷ (λ _ → Set) ⟧ᵗ} {i : ⟦ [] ▷ (λ _ → ℕ) ⟧ᵗ}
--          → Vec (snd p) (snd i) → ⟦ VecD' p ⟧ˢ (Vec (snd p) ∘ snd) i
-- fromVec' []       = inl                    refl
-- fromVec' (a ∷ as) = inr (inl (a , _ , as , refl))

-- VecParamO : (p q : ⟦ [] ▷ (λ _ → Set) ⟧ᵗ)
--           → (snd p → snd q)
--          → SetO (VecD' p) (VecD' q)
-- VecParamO (_ , A) (_ , B) f = record
--   { param = λ _ → tt
--   ; index = λ _ i → i
--   ; applyP   = λ _ → ι refl
--               ∷ ◂ Δ (λ a → ∇ (f a) (σ λ n → ρ (ι refl) (ι refl)))
--               ∷ ◂ [] }

-- vmap-base : {A B : Set} → (A → B)
--           → ({n : ℕ} → Vec A n → Vec B n)
--           → ({n : ℕ} → Vec A n → Vec B n)
-- vmap-base {A} {B} f rec =
--   toVec' ∘ eraseˢ (VecParamO (tt , A) (tt , B) f) ∘ fmapˢ (VecD' (tt , A)) rec ∘ fromVec'

-- vmap : {A B : Set} → (A → B) → {n : ℕ} → Vec A n → Vec B n
-- vmap f []       = {! vmap-base f (vmap f) [] !}
-- vmap f (x ∷ xs) = {! vmap-base f (vmap f) (x ∷ xs) !}
