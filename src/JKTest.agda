{-# OPTIONS --safe #-}

open import Prelude
open import Generics.Safe.Telescope hiding (∷-syntaxᵗ)
open ∀ℓ; open ∀ℓω; open ∀ᵗ; open ∀ᵇᵗ
open import Generics.Safe.Description
open import Generics.Safe.Description.FixedPoint
open import Generics.Safe.Algebra
open import Generics.Safe.Ornament
open import Generics.Safe.Ornament.Description
open import Generics.Safe.Ornament.Algebraic
open import Generics.Safe.Ornament.Promotion
open import Generics.Safe.Recursion
open import Generics.Safe.RecursionScheme
open import Generics.Safe.InductiveEquality

-- USER: ℕ

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
foldℕ-alg : ∀ℓω 0 λ ℓs → {ℓ : Level} → ∀ᵇᵗ false [] λ ps →
            {X : ∀ᵇᵗ false [] λ _ → Set ℓ} →
            ∀ᵗ true ((X $$ tt) ∷ λ _ → (X $$ tt → X $$ tt) ∷ λ _ → []) λ _ →
            Algebra (ι tt ∷ ρ (ι tt) (ι tt) ∷ []) ℓ
-- foldℕ-alg : {! ∀ℓω _ λ ℓs → ∀ {ℓ} → ∀ᵗ false _ λ ps → FoldAlgTᵈ NatD ℓs ps ℓ !}
foldℕ-alg = fold-algᵈ NatD

-- META
foldℕ-wrapper : ∀ℓω 0 λ ℓs → {ℓ : Level} → ∀ᵗ false [] λ ps →
                {X : ∀ᵗ false [] λ _ → Set ℓ} →
                ∀ᵗ true ((X $$ tt) ∷ λ _ → (X $$ tt → X $$ tt) ∷ λ _ → []) λ args →
                FoldT NatC (foldℕ-alg $$ ℓs $$ ps $$ args)
foldℕ : {ℓ : Level} {X : Set ℓ} → X → (X → X) → ℕ → X

-- META
foldℕ-wrapper $$ _ $$ _ $$ z , s , _ = foldℕ z s
foldℕ z s  zero   = z
foldℕ z s (suc n) = s (foldℕ z s n)
-- foldℕ z s  zero   = {! (fold-base NatC (foldℕ-alg $$ _ $$ _ $$ z , s , _) (foldℕ-wrapper $$ _ $$ _ $$ (z , s , _)) $$ _)  zero   !}
-- foldℕ z s (suc n) = {! (fold-base NatC (foldℕ-alg $$ _ $$ _ $$ z , s , _) (foldℕ-wrapper $$ _ $$ _ $$ (z , s , _)) $$ _) (suc n) !}

-- USER (changing the form of the fold)
-- foldℕ : ∀ {ℓ} (X : Set ℓ) → (X → X) → X → ℕ → X
-- foldℕ X s z  zero   = z
-- foldℕ X s z (suc n) = s (foldℕ X s z n)
-- (foldℕ-wrapper $$ _ $$ _ $$ (z , s , _) $$ _) n = foldℕ _ s z n

-- META
foldℕ-is-fold : ∀ {ℓs ps ℓ} {X : Set ℓ} (z : X) (s : X → X)
              → AlgC NatC (foldℕ-alg     $$ ℓs $$ ps $$ (z , s , _))
                          (foldℕ-wrapper $$ ℓs $$ ps $$ (z , s , _))
foldℕ-is-fold z s (inl           refl  ) = refl
foldℕ-is-fold z s (inr (inl (_ , refl))) = refl

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

-- META
ListD : DataD
ListD = record
  { #levels = 1
  ; applyL  = λ ℓs → let (ℓ , _) = ℓs in record
      { alevel = ℓ
      ; level-pre-fixed-point = refl
      ; Param  = [ A ∶ Set ℓ ] []
      ; Index  = λ _ → []
      ; applyP = λ ps → let (A , _) = ps
                        in (ι tt)
                         ∷ (σ A λ _ → ρ (ι tt) (ι tt))
                         ∷ [] } }

-- META
List-wrapper : DataT ListD
List-wrapper (ℓ , _) (A , _) _ = List A

-- META
ListC : DataC ListD List-wrapper
ListC = record
  { toN   = λ { (inl                refl  ) → []
              ; (inr (inl (a , as , refl))) → a ∷ as }
  ; fromN = λ { []       → inl                refl
              ; (a ∷ as) → inr (inl (a , as , refl)) }
  ; fromN-toN = λ { (inl                refl  ) → refl
                  ; (inr (inl (a , as , refl))) → refl }
  ; toN-fromN = λ { []       → refl
                  ; (a ∷ as) → refl } }

-- USER
ListD/NatD : DataO ListD NatD
ListD/NatD = record
  { level  = λ _ → tt
  ; applyL = λ ℓs → let (ℓ , _) = ℓs in record
      { param  = λ _ → tt
      ; index  = λ _ _ → tt
      ; applyP = λ _ → (ι refl)
                   ∷ ∺ (Δ λ _ → ρ (ι refl) (ι refl))
                   ∷ ∺ [] } }

-- USER
length-alg : ∀ℓ _ λ ℓs → ∀ᵇᵗ false _ λ ps → Algebraᵈ ListD ℓs ps 0ℓ
length-alg = forget-alg ListD/NatD NatC

-- META
length'-wrapper : ∀ℓ _ λ ℓs → ∀ᵗ false _ λ ps → FoldT ListC (length-alg $$ ℓs $$ ps)
length' : {A : Set ℓ} → List A → ℕ   -- slightly modified by the user
length'-wrapper $$ _ $$ _ = length'  -- also slightly modified
length' []       = 0
length' (a ∷ as) = suc (length' as)
length'C : ∀ ℓs ps → AlgC ListC (length-alg $$ ℓs $$ ps) (length'-wrapper $$ ℓs $$ ps)
length'C ℓs ps (inl                refl  ) = refl
length'C ℓs ps (inr (inl (a , as , refl))) = refl
-- length'-wrapper = length'
-- length' []       = {! (fold-base ListC (length-alg $$ _ $$ _) (length'-wrapper $$ _ $$ _) $$ _) []       !}
-- length' (a ∷ as) = {! (fold-base ListC (length-alg $$ _ $$ _) (length'-wrapper $$ _ $$ _) $$ _) (a ∷ as) !}

-- USER
VecOD : DataOD ListD
VecOD = algOD ListD (λ ℓs ps → length-alg $$ ℓs $$ ps)

VecD : DataD
VecD = ⌊ VecOD ⌋ᵈ

-- META (slightly modified by the user)
data Vec (A : Set ℓ) : ℕ → Set ℓ where
  []  : Vec A zero
  _∷_ : A → {n : ℕ} → Vec A n → Vec A (suc n)

-- -- META
-- VecD : DataD
-- VecD = record
--   { #levels = 1
--   ; applyL  = λ ℓs → let (ℓ , _) = ℓs in record
--       { alevel = ℓ
--       ; level-pre-fixed-point = refl
--       ; Param  = [ A ∶ Set ℓ ] []
--       ; Index  = λ _ → [ _ ∶ ℕ ] []
--       ; applyP = λ ps → let (A , _) = ps
--                         in (ι (0 , _))
--                          ∷ (σ A λ _ → σ ℕ λ n → ρ (ι (n , _)) (ι (suc n , _)))
--                          ∷ [] } }

-- META
Vec-wrapper : DataT VecD
Vec-wrapper (ℓ , _) (A , _) (_ , n) = Vec A n

-- META
VecC : DataC VecD Vec-wrapper
VecC = record
  { toN   = λ { (inl                    refl  ) → []
              ; (inr (inl (a , n , as , refl))) → a ∷ as }
  ; fromN = λ { []       → inl                    refl
              ; (a ∷ as) → inr (inl (a , _ , as , refl)) }
  ; fromN-toN = λ { (inl                    refl  ) → refl
                  ; (inr (inl (a , n , as , refl))) → refl }
  ; toN-fromN = λ { []       → refl
                  ; (a ∷ as) → refl } }

-- USER
Vec-remember-alg : ∀ℓ 1 λ ℓs → ∀ᵇᵗ false (Set (fst ℓs) ∷ (λ A → [])) λ ps
                 → IndAlgebraᵈ ListC ℓs ps (fst ℓs)
Vec-remember-alg =
  remember-alg ListC (λ ℓs ps → length-alg      $$ ℓs $$ ps)
                     (λ ℓs ps → length'-wrapper $$ ℓs $$ ps) length'C VecC

-- META
Vec-remember-wrapper : ∀ℓ 1 λ ℓs → ∀ᵗ false (Set (fst ℓs) ∷ (λ A → [])) λ ps
                     → IndT ListC (Vec-remember-alg $$ ℓs $$ ps)
Vec-remember : {ℓ : Level} {A : Set ℓ} (as : List A) → Vec A (length' as)
Vec-remember-wrapper $$ _ $$ _ = Vec-remember
Vec-remember []       = []
Vec-remember (a ∷ as) = a ∷ Vec-remember as
Vec-rememberC : ∀ ℓs ps → IndAlgC ListC (Vec-remember-alg     $$ ℓs $$ ps)
                                        (Vec-remember-wrapper $$ ℓs $$ ps)
Vec-rememberC ℓs ps (inl                refl  ) = refl
Vec-rememberC ℓs ps (inr (inl (a , as , refl))) = refl
-- Vec-remember {ℓ} {A} []       = {! ind-base ListC (Vec-remember-alg $$ ℓ , _ $$ A , _) (Vec-remember-wrapper $$ ℓ , _ $$ A , _) []       !}
-- Vec-remember {ℓ} {A} (a ∷ as) = {! ind-base ListC (Vec-remember-alg $$ ℓ , _ $$ A , _) (Vec-remember-wrapper $$ ℓ , _ $$ A , _) (a ∷ as) !}

data W {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  sup : (a : A) → (B a → W A B) → W A B

data IEqW {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} : W A B → W A B → Set (ℓ ⊔ ℓ') where
  sup : (a : A) → {x y : B a → W A B}
                → ((b : B a) → IEqW (x b) (y b)) → IEqW (sup a x) (sup a y)

w₀ w₁ : W Bool λ b → if b then Bool else ⊥
w₀ = sup true λ _ → sup false λ ()
w₁ = sup true λ { false → sup false λ (); true → sup false λ () }

-- w₀≡w₁ : w₀ ≡ w₁
-- w₀≡w₁ = {! refl !}

IEqW-w₀-w₁ : IEqW w₀ w₁
IEqW-w₀-w₁ = sup true (λ { false → sup false λ (); true → sup false λ () })

fromIEqW : FunExt → {A : Set ℓ} {B : A → Set ℓ'} {x y : W A B} → IEqW x y → x ≡ y
fromIEqW funext (sup a e) = cong (sup a) (funext λ b → fromIEqW funext (e b))

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
