{-# OPTIONS --safe --with-K #-}

module Examples.WithMacros.STLC where

open import Prelude

open import Generics.Description
open import Generics.Recursion
open import Generics.Reflection

open import Generics.Ornament
open import Generics.Ornament.Description
open import Generics.Ornament.Algebraic
open import Generics.Ornament.Algebraic.Isomorphism

open import Examples.WithMacros.Nat
open import Examples.WithMacros.List

--------
-- Untyped λ-calculus

data Λ : Set where
  var : ℕ → Λ
  app : Λ → Λ → Λ
  lam : Λ → Λ

UntypedTermD = genDataD Λ
UntypedTermT = genDataT UntypedTermD Λ
UntypedTermC = genDataC UntypedTermD UntypedTermT

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
TypedTermT = genDataT TypedTermD _⊢_
TypedTermC = genDataC TypedTermD TypedTermT

TypedTermO : DataO TypedTermD UntypedTermD
TypedTermO = record
  { level  = λ _ → tt
  ; applyL = λ _ → record
      { param  = λ _ → tt
      ; index  = λ _ _ → tt
      ; applyP = λ _ → (Δ[ Γ ] Δ[ τ ] Δ[ i ] ∇ (toℕ i) ι)
                  ∷ ∺ (Δ[ Γ ] Δ[ τ ] Δ[ τ' ] ρ ι (ρ ι ι))
                  ∷ ∺ (Δ[ τ ] Δ[ Γ ] Δ[ τ' ] ρ ι ι) ∷ ∺ [] } }

TypedTermFin : Finitary TypedTermD
TypedTermFin = (tt ∷ tt ∷ tt ∷ [])
             ∷ (tt ∷ tt ∷ tt ∷ refl ∷ refl ∷ [])
             ∷ (tt ∷ tt ∷ tt ∷ refl ∷ []) ∷ []

private
  toΛP : FoldP
  toΛP = forget TypedTermC UntypedTermC TypedTermO

unquoteDecl toΛ = defineFold toΛP toΛ
-- toΛ : Γ ⊢ τ → Λ
-- toΛ (var i  ) = var (toℕ i)
-- toΛ (app t u) = app (toΛ t) (toΛ u)
-- toΛ (lam t  ) = lam (toΛ t)

instance toΛC = genFoldC toΛP toΛ

--------
-- Typing relation as an algebraic ornamentation

private
  TypingOD : DataOD TypedTermD
  TypingOD = AlgOD toΛP

TypingO = ⌈ TypingOD ⌉ᵈ

infix 3 _⊢_∶_

unquoteDecl data Typing constructor c0 c1 c2 = defineByDataD ⌊ TypingOD ⌋ᵈ Typing (c0 ∷ c1 ∷ c2 ∷ [])
_⊢_∶_ : List Ty → Λ → Ty → Set
_⊢_∶_ a b c = Typing a c b
--data _⊢_∶_ : List Ty → Λ → Ty → Set₀ where
--
--  var : (i : Γ ∋ τ)
--      → -------------------
--        Γ ⊢ var (toℕ i) ∶ τ
--
--  app : ∀ {t} → Γ ⊢ t ∶ τ ⇒ τ'
--      → ∀ {u} → Γ ⊢ u ∶ τ
--      → ----------------------
--        Γ ⊢ app t u ∶ τ'
--
--  lam : ∀ {t} → τ ∷ Γ ⊢ t ∶ τ'
--      → ----------------------
--        Γ ⊢ lam t ∶ τ ⇒ τ'

TypingD = ⌊ TypingOD ⌋ᵈ

TypingT : DataT TypingD
TypingT tt tt ((Γ , τ , tt) , t , tt) = Γ ⊢ t ∶ τ

TypingC = genDataC TypingD TypingT

--------
-- Conversion between intrinsically and extrinsically typed terms

private
  fromTypingP : FoldP
  fromTypingP = forget TypingC TypedTermC ⌈ TypingOD ⌉ᵈ

unquoteDecl fromTyping = defineFold fromTypingP fromTyping
-- fromTyping : ∀ {t} → Γ ⊢ t ∶ τ → Γ ⊢ τ
-- fromTyping (var i  ) = var i
-- fromTyping (app d e) = app (fromTyping d) (fromTyping e)
-- fromTyping (lam d  ) = lam (fromTyping d)

fromTypingC = genFoldC fromTypingP fromTyping

private
  toTypingP : IndP
  toTypingP = remember toΛC TypingC

unquoteDecl toTyping = defineInd toTypingP toTyping
-- toTyping : (t : Γ ⊢ τ) → Γ ⊢ toΛ t ∶ τ
-- toTyping (var i  ) = var i
-- toTyping (app t u) = app (toTyping t) (toTyping u)
-- toTyping (lam t  ) = lam (toTyping t)

instance toTypingC = genIndC toTypingP toTyping

--private
--  from-toTypingP : IndP
--  from-toTypingP = forget-remember-inv toΛC TypingC fromTypingC toTypingC (inl TypedTermFin)

--unquoteDecl from-toTyping = defineInd from-toTypingP from-toTyping
-- from-toTyping : (t : Γ ⊢ τ) → fromTyping (toTyping t) ≡ t
-- from-toTyping (var i  ) = refl
-- from-toTyping (app t u) = trans' (cong (app (fromTyping (toTyping t))) (from-toTyping u))
--                                  (cong (λ n' → app n' u) (from-toTyping t))
-- from-toTyping (lam t  ) = cong lam (from-toTyping t)

--from-toTypingC = genIndC from-toTypingP from-toTyping

--private
--  to-fromTypingP : IndP
--  to-fromTypingP = remember-forget-inv toΛC TypingC fromTypingC toTypingC (inl TypedTermFin)

--unquoteDecl to-fromTyping = defineInd to-fromTypingP to-fromTyping
-- to-fromTyping : ∀ {t} (d : Γ ⊢ t ∶ τ)
--               → (toΛ (fromTyping d) , toTyping (fromTyping d))
--               ≡ ((t , d) ⦂ Σ[ t' ∈ Λ ] Γ ⊢ t' ∶ τ)  -- [FAIL] manual type annotation
-- to-fromTyping (var i) = refl
-- to-fromTyping (app {Γ} {τ} {τ'} {t} d e) =
--   trans
--    (cong
--     (bimap (λ x → x) (DataC.toN (findDataC (quote _⊢_∶_))))
--     (cong (bimap (λ x → x) inr)
--      (cong (bimap (λ x → x) inl)
--       (cong (bimap (λ x → x) (λ section → Γ , section))
--        (cong (bimap (λ x → x) (λ section → τ , section))
--         (cong (bimap (λ x → x) (λ section → τ' , section))
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
--     (bimap (λ x → x) (DataC.toN (findDataC (quote _⊢_∶_))))
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

--to-fromTypingC = genIndC to-fromTypingP to-fromTyping
