{-# OPTIONS --safe --with-K #-}

module Examples.WithMacros.Acc where

open import Prelude hiding (lookupAny)

open import Generics.Description
open import Generics.Recursion
open import Generics.Reflection

open import Generics.RecursionScheme
open import Generics.SimpleContainer
open import Generics.SimpleContainer.Any

data Acc {A : Set ℓ} (R : A → A → Set ℓ') : A → Set (ℓ ⊔ ℓ') where
  acc : {x : A} → ((y : A) → R y x → Acc R y) → Acc R x

--------
-- Strong induction as the fold operator on Acc

AccD = genDataD Acc
AccC = genDataC AccD (genDataT AccD Acc)

private
  foldAccP : FoldP
  foldAccP = fold-operator AccC

unquoteDecl foldAcc = defineFold foldAccP foldAcc
-- foldAcc :
--   ∀ {ℓ'' ℓ ℓ'} {A : Set ℓ} {R : A → A → Set ℓ'} {P : A → Set ℓ''}
--   → ((x : A) → ((y : A) → R y x → P y) → P x)
--   → (x : A) → Acc R x → P x
-- foldAcc p x (acc accs) = p x (λ y r → foldAcc p y (accs y r))

foldAccC = genFoldC foldAccP foldAcc

--------
-- Descending chains in terms of the Any predicate

instance
  AccS : SCᵈ AccD
  AccS = record
    { El  = λ (A , _) → A
    ; pos = (true ∷ tt ∷ []) ∷ []
    ; coe = λ _ → (refl ,ωω λ _ → lift tt) ,ωω lift tt }

private
  AccAnyD : DataD
  AccAnyD = AnyD AccC AccS

unquoteDecl data AccAny constructor c0 c1 = defineByDataD AccAnyD AccAny (c0 ∷ c1 ∷ [])
-- data AccAny {ℓ'' ℓ ℓ'} {A : Set ℓ} {R : A → A → Set ℓ'}
--   (P : A → Set ℓ'') : (x : A) → Acc R x → Set (ℓ ⊔ ℓ' ⊔ ℓ'') where
--   here  : ∀ {x accs} → P x → AccAny P x (acc accs)
--   there : ∀ {x accs y} (r : R y x)
--         → AccAny P y (accs y r) → AccAny P x (acc accs)

AccAnyT = genDataT AccAnyD AccAny
AccAnyC = genDataC AccAnyD AccAnyT

private
  lookupAnyAccP : FoldP
  lookupAnyAccP = lookupAny AccC AccS AccAnyC

unquoteDecl lookupAnyAcc = defineFold lookupAnyAccP lookupAnyAcc
-- lookupAnyAcc :
--   ∀ {ℓ'' ℓ ℓ'} {A : Set ℓ} {R : A → A → Set ℓ'} {P : A → Set ℓ''}
--   {x : A} {a : Acc R x} → AccAny P x a → Σ A P
-- lookupAnyAcc (here p   ) = _ , p
-- lookupAnyAcc (there _ i) = lookupAnyAcc i

lookupAnyAccC = genFoldC lookupAnyAccP lookupAnyAcc
