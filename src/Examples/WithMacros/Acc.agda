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

instance
  AccC : Named (quote Acc) _
  unNamed AccC = genDataC AccD (genDataT AccD Acc)
    where AccD = genDataD Acc

private
  foldAccP : FoldP
  foldAccP = fold-operator (quote Acc)

unquoteDecl foldAcc = defineFold foldAccP foldAcc
--foldAcc :
--  ∀ {ℓ'' ℓ ℓ'} {A : Set ℓ} {R : A → A → Set ℓ'} {P : A → Set ℓ''}
--  → ((x : A) → ((y : A) → R y x → P y) → P x)
--  → (x : A) → Acc R x → P x
--foldAcc p x (acc accs) = p x (λ y r → foldAcc p y (accs y r))

instance foldAccC = genFoldC foldAccP foldAcc

--------
-- Descending chains in terms of the Any predicate

instance
  AccS : SCᵈ (findDataD (quote Acc))
  AccS = record
    { El  = λ (A , _) → A
    ; pos = (true ∷ tt ∷ []) ∷ []
    ; coe = λ _ → (refl ,ωω λ _ → lift tt) ,ωω lift tt }

private
  AccAnyD : DataD
  AccAnyD = AnyD (quote Acc)

unquoteDecl data AccAny constructor accany0 accany1 = defineByDataD AccAnyD AccAny (accany0 ∷ accany1 ∷ [])
--data AccAny {ℓ'' ℓ ℓ'} {A : Set ℓ} {R : A → A → Set ℓ'}
--  (P : A → Set ℓ'') : (x : A) → Acc R x → Set (ℓ ⊔ ℓ' ⊔ ℓ'') where
--  here  : ∀ {x accs} → P x → AccAny P x (acc accs)
--  there : ∀ {x accs y} (r : R y x)
--        → AccAny P y (accs y r) → AccAny P x (acc accs)

instance
  AccAnyC : Named (quote AccAny) _
  unNamed AccAnyC = genDataC AccAnyD AccAnyT
    where AccAnyT = genDataT AccAnyD AccAny

private
  lookupAnyAccP : FoldP
  lookupAnyAccP = lookupAny (quote Acc)

unquoteDecl lookupAnyAcc = defineFold lookupAnyAccP lookupAnyAcc
-- lookupAnyAcc :
--   ∀ {ℓ'' ℓ ℓ'} {A : Set ℓ} {R : A → A → Set ℓ'} {P : A → Set ℓ''}
--   {x : A} {a : Acc R x} → AccAny P x a → Σ A P
-- lookupAnyAcc (here p   ) = _ , p
-- lookupAnyAcc (there _ i) = lookupAnyAcc i

instance lookupAnyAccC = genFoldC lookupAnyAccP lookupAnyAcc
