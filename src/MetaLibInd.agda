open import Agda.Builtin.Reflection
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.List

open import Agda.Primitive

open import Reflection
open import Function.Base using (case_of_)
open import Data.Maybe using (Maybe)

open import InductionUniverse

open import Data.Vec

mutual
  _Tel++_ : ∀ {A B ℓ} → Tel A ℓ → Tel B ℓ → Tel _ ℓ
  t1 Tel++ nil       = t1
  t1 Tel++ snoc t2 a = snoc (t1 Tel++ t2) λ { (fst₁ , snd₁) → a ({!!} , {!!})}

  splitTel : ∀ {ℓ} {t1 : Tel _ ℓ} {t2 : Tel _ ℓ} {A} → ⟦ _Tel++_ t1 t2 ⟧ᵗ A → Σ {!!} ⟦ t2 ⟧ᵗ
  splitTel {t1 = t1} {t2 = nil} t = {!!} , tt
  splitTel {t1 = t1} {t2 = snoc t2 A} t = {!!} , {!!} , {!!}

piToTel : Type → TC (Tel _ _)
piToTel (pi (arg i x) (abs s y)) = do x' ← unquoteTC x
                                      ys' ← piToTel y
                                      case ys' of λ where
                                        nil → return (snoc nil x')
                                        (snoc _ z) → return (snoc {!!} z)
piToTel t        = return nil

parseParam : Type → Nat → TC (Σ (Tel₀ _) λ P → Tel ⟦ P ⟧ᵗ⁰ _)
parseParam typ n = {!!}

parseData : Name → TC Clauses
parseData dataName = do d ← getDefinition dataName
                        case d of λ where
                          (data-type pars cs) → do t ← getType dataName
                                                   {!!}
                          _ → typeError (strErr "Given name is not of a datatype definition." ∷ [])
