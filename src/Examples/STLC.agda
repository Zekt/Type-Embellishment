{-# OPTIONS --safe --with-K #-}

module Examples.STLC where

open import Prelude

open import Generics.Description
open import Generics.Recursion
open import Generics.Reflection

open import Generics.Ornament
open import Generics.Ornament.Description
open import Generics.Ornament.Algebraic
open import Generics.Ornament.Algebraic.Isomorphism

open import Examples.Nat
open import Examples.List

--------
-- Untyped λ-calculus

data Λ : Set where
  var : ℕ → Λ
  app : Λ → Λ → Λ
  lam : Λ → Λ

UntypedTermD = genDataD Λ
UntypedTermC = genDataC UntypedTermD (genDataT UntypedTermD Λ)

--------
-- Simply typed λ-calculus

infixr 5 _⇒_

data Ty : Set where
  base : Ty
  _⇒_  : Ty → Ty → Ty

variable
  τ τ' : Ty
  Γ    : List Ty

infix 3 _⊢_

data _⊢_ : List Ty → Ty → Set where

  var : Γ ∋ τ
      → -----
        Γ ⊢ τ

  app : Γ ⊢ τ ⇒ τ'
      → Γ ⊢ τ
        ----------
      → Γ ⊢ τ'

  lam : τ ∷ Γ ⊢ τ'
      → ----------
        Γ ⊢ τ ⇒ τ'

TypedTermD = genDataD _⊢_
TypedTermC = genDataC TypedTermD (genDataT TypedTermD _⊢_)

TypedTermO : DataO TypedTermD UntypedTermD
TypedTermO = record
  { level  = λ _ → tt
  ; applyL = λ _ → record
      { param  = λ _ → tt
      ; index  = λ _ _ → tt
      ; applyP = λ _ → (Δ[ Γ ] Δ[ τ ] Δ[ i ] ∇ (toℕ i) ι)
                   ∷ ∺ (Δ[ Γ ] Δ[ τ ] Δ[ τ' ] ρ ι (ρ ι ι))
                   ∷ ∺ (Δ[ τ ] Δ[ Γ ] Δ[ τ' ] ρ ι ι) ∷ ∺ [] } }

toΛP : FoldP
toΛP = forget TypedTermC UntypedTermC TypedTermO

-- unquoteDecl toΛ = defineFold toΛP toΛ
toΛ : Γ ⊢ τ → Λ
toΛ (var i  ) = var (toℕ i)
toΛ (app t u) = app (toΛ t) (toΛ u)
toΛ (lam t  ) = lam (toΛ t)

toΛC = genFoldC toΛP toΛ

TypedTermFin : Finitary TypedTermD
TypedTermFin _ = (tt ∷ tt ∷ tt ∷ [])
               ∷ (tt ∷ tt ∷ tt ∷ refl ∷ refl ∷ [])
               ∷ (tt ∷ tt ∷ tt ∷ refl ∷ []) ∷ []

--------
-- Typing relation as an algebraic ornamentation

TypingOD : DataOD TypedTermD
TypingOD = AlgOD toΛP

infix 3 _⊢_∶_

-- unquoteDecl data Typing constructor var' app' lam' =
--   defineByDataD ⌊ TypingOD ⌋ᵈ Typing (var' ∷ app' ∷ lam' ∷ [])
data _⊢_∶_ : List Ty → Λ → Ty → Set₀ where

  var : (i : Γ ∋ τ)
      → -------------------
        Γ ⊢ var (toℕ i) ∶ τ

  app : ∀ {t} → Γ ⊢ t ∶ τ ⇒ τ'
      → ∀ {u} → Γ ⊢ u ∶ τ
      → ----------------------
        Γ ⊢ app t u ∶ τ'
  lam : ∀ {t} → τ ∷ Γ ⊢ t ∶ τ'
      → ----------------------
        Γ ⊢ lam t ∶ τ ⇒ τ'

TypingT : DataT ⌊ TypingOD ⌋ᵈ
TypingT tt tt ((x , x₁ , tt) , x₂ , tt) = x ⊢ x₂ ∶ x₁

TypingC = genDataC ⌊ TypingOD ⌋ᵈ TypingT

--------
-- Conversion between intrinsically and extrinsically typed terms

fromTypingP : FoldP
fromTypingP = forget TypingC TypedTermC ⌈ TypingOD ⌉ᵈ

-- unquoteDecl fromTyping = defineFold fromTypingP fromTyping
fromTyping : ∀ {t} → Γ ⊢ t ∶ τ → Γ ⊢ τ
fromTyping (var i  ) = var i
fromTyping (app d e) = app (fromTyping d) (fromTyping e)
fromTyping (lam d  ) = lam (fromTyping d)

fromTypingC = genFoldC fromTypingP fromTyping

toTypingP : IndP
toTypingP = remember toΛC TypingC

-- unquoteDecl toTyping = defineInd toTypingP toTyping
toTyping : (t : Γ ⊢ τ) → Γ ⊢ toΛ t ∶ τ
toTyping (var i  ) = var i
toTyping (app t u) = app (toTyping t) (toTyping u)
toTyping (lam t  ) = lam (toTyping t)

toTypingC = genIndC toTypingP toTyping

from-toTypingP : IndP
from-toTypingP = forget-remember-inv toΛC TypingC fromTypingC toTypingC (inl TypedTermFin)

unquoteDecl from-toTyping = defineInd from-toTypingP from-toTyping
-- from-toTyping : (t : Γ ⊢ τ) → fromTyping (toTyping t) ≡ t
-- from-toTyping (var i) = refl
-- from-toTyping (app {Γ} {τ} {τ'} t u) =
--   trans
--    (cong (DataC.toN TypedTermC)
--     (cong inr
--      (cong inl
--       (cong (λ section → Γ , section)
--        (cong (λ section → τ , section)
--         (cong (λ section → τ' , section)
--          (cong₂ _,_ (from-toTyping t)
--           (cong₂ _,_ (from-toTyping u) refl))))))))
--    refl
-- from-toTyping (lam {τ} {Γ} {τ'} t) =
--   trans
--    (cong (DataC.toN TypedTermC)  -- [FAIL] manually un-normalised
--     (cong inr
--      (cong inr
--       (cong inl
--        (cong (λ section → τ , section)
--         (cong (λ section → Γ , section)
--          (cong (λ section → τ' , section)
--           (cong₂ _,_ (from-toTyping t)
--            refl))))))))
--    refl

from-toTypingC = genIndC from-toTypingP from-toTyping

to-fromTypingP : IndP
to-fromTypingP = remember-forget-inv toΛC TypingC toTypingC fromTypingC (inl TypedTermFin)

-- [FAIL] too slow; manually case-split and elaborate-and-give
unquoteDecl to-fromTyping = defineInd to-fromTypingP to-fromTyping
-- to-fromTyping : ∀ {t} (d : Γ ⊢ t ∶ τ)
--               → (toΛ (fromTyping d) , toTyping (fromTyping d))
--               ≡ ((t , d) ⦂ Σ[ t' ∈ Λ ] Γ ⊢ t' ∶ τ)  -- [FAIL] manual type annotation
-- to-fromTyping (var i) = refl
-- to-fromTyping (app {Γ} {τ} {τ'} {t} d e) =
--   trans
--    (cong
--     (bimap (λ x → x) (DataC.toN TypingC))  -- [FAIL] manually un-normalised
--     (cong (bimap (λ x → x) inr)
--      (cong (bimap (λ x → x) inl)
--       (cong (bimap (λ x → x) (λ section → Γ , section))
--        (cong (bimap (λ x → x) (λ section → τ , section))
--         (cong (bimap (λ x → x) (λ section → τ' , section))  -- [FAIL] printed as τ (if implicit arguments to app are not given on lhs)
--          (trans
--           (cong
--            (λ p →
--               app (fst p) (toΛ (fromTyping e)) ,
--               fst p ,
--               snd p , toΛ (fromTyping e) , toTyping (fromTyping e) , refl)
--            (to-fromTyping d))
--           (cong (bimap (λ x → x) (λ x → t , d , x))
--            (trans
--             (cong (λ p → app t (fst p) , fst p , snd p , refl)
--              (to-fromTyping e))
--             refl)))))))))
--    refl
-- to-fromTyping (lam {τ} {Γ} {τ'} d) =
--   trans
--    (cong
--     (bimap (λ x → x) (DataC.toN TypingC))  -- [FAIL] manually un-normalised
--     (cong (bimap (λ x → x) inr)
--      (cong (bimap (λ x → x) inr)
--       (cong (bimap (λ x → x) inl)
--        (cong (bimap (λ x → x) (λ section → τ , section))
--         (cong (bimap (λ x → x) (λ section → Γ , section))
--          (cong (bimap (λ x → x) (λ section → τ' , section))
--           (trans
--            (cong (λ p → lam (fst p) , fst p , snd p , refl) (to-fromTyping d))
--            refl))))))))
--    refl

to-fromTypingC = genIndC to-fromTypingP to-fromTyping
