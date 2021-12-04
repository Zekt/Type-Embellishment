module MetaLib.MetaLibInd where

open import Prelude

open import Universe.InductiveUniverse
--open import Telescope
open import Utils

open import Data.Vec
  hiding (initLast)

data FinList : {A : Set} {m : ℕ} → (n : ℕ) → Vec A m → Set where
  same : ∀ {n} {A : Set} {v : Vec A n} → FinList n v
  succ : ∀ {n} {A : Set} {v : Vec A n} → FinList (suc n) v

lookupTel : (tel : Tel₀ ℓ) → ℕ → Maybe (⟦ tel ⟧ᵗ⁰ → Set ℓ)
lookupTel nil n = nothing
lookupTel (snoc tel A) zero = just λ x → A (tt , fst x)
lookupTel (snoc tel A) (suc n) = maybe′ (λ f → just (f ∘ fst)) nothing (lookupTel tel n)

piToTel : Tel₀ ℓ → Type → TC (Tel₀ ℓ)
piToTel tel (pi (arg i x) (abs s y)) = do
  x' ← unquoteTC x
  let newtel = maybe′ (λ f → snoc tel λ {(tt , ⟦tel⟧) → f ⟦tel⟧})
                      {!!}
                      (lookupTel tel {!!})
  return (snoc (snoc nil (const x')) λ { (_ , _ , x') →
                                           case y of {!!}})
--  xs' ← piToTel x
--  ys' ← piToTel y
--  case ys' of λ where
--    nil → return {!!}
--    (snoc ztel _) → return (snoc ztel {!!})
piToTel tel t        = do t ← unquoteTC t
                          return (snoc nil λ _ → t)

{-# TERMINATING #-}
typesToTel : List Type → Type → TC (Tel₀ ℓ)
typesToTel cxt t with snocView cxt
... | []       = {!!}
... | xs ∷ʳ x = do
  telTel ← typesToTel xs x
  return (snoc telTel λ { (tt , b) → {!!}})

parseParam : Type → ℕ → TC (Σ (Tel₀ ℓ) λ P → Tel ⟦ P ⟧ᵗ⁰ ℓ)
parseParam typ n = {!!}

parseData : Name → TC Clauses
parseData dataName = do d ← getDefinition dataName
                        case d of λ where
                          (data-type pars cs) → do t ← getType dataName
                                                   {!!}
                          _ → typeError (strErr "Given name is not of a datatype definition." ∷ [])
