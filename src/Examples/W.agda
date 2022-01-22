{-# OPTIONS --safe --with-K #-}

module Examples.W where

open import Prelude hiding (lookupAny)

open import Generics.Description
open import Generics.Recursion
open import Generics.Reflection

open import Generics.RecursionScheme
open import Generics.Ornament
open import Generics.Ornament.Description
open import Generics.Ornament.Algebraic
open import Generics.SimpleContainer
open import Generics.SimpleContainer.Any

data W (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  sup : (a : A) → (B a → W A B) → W A B

WD = genDataD W
WC = genDataC WD (genDataT WD W)

--------
-- Transfinite induction

-- unquoteDecl indW = defineInd (ind-operator WC) indW
indW : {A : Set ℓ} {B : A → Set ℓ'} (P : W A B → Set ℓ'')
     → ((a : A) (ws : B a → W A B) → ((b : B a) → P (ws b)) → P (sup a ws))
     → (w : W A B) → P w
indW P s (sup a ws) = s a ws (λ b → indW P s (ws b))

indWT : IndT (ind-operator WC)
indWT _ ((a , a₁ , tt) , a₂ , a₃ , tt) = indW a₂ a₃

indWC = genIndC (ind-operator WC) indWT

--------
-- Any predicate

WS : SCᵈ WD
WS _ = record
  { El  = λ (A , _) → A
  ; pos = (true ∷ tt ∷ []) ∷ []
  ; coe = λ _ → (refl ,ωω λ _ → lift tt) ,ωω lift tt }

WAnyD : DataD
WAnyD = ⌊ AnyOD WC WS ⌋ᵈ

-- unquoteDecl data WAny constructor c0 c1 = defineByDataD WAnyD WAny (c0 ∷ c1 ∷ [])
data WAny {A : Set ℓ} {B : A → Set ℓ'} (P : A → Set ℓ'') : W A B → Set (ℓ ⊔ ℓ' ⊔ ℓ'') where
  here  : ∀ {a ws} → P a → WAny P (sup a ws)
  there : ∀ {a ws} (b : B a) → WAny P (ws b) → WAny P (sup a ws)

WAnyT : DataT WAnyD
WAnyT _ ((A , B , tt) , P , tt) (tt , x , tt) = WAny P x

WAnyC = genDataC WAnyD WAnyT

lookupWAnyP : FoldP
lookupWAnyP = lookupAny WC WS WAnyC

-- unquoteDecl lookupWAny = defineFold lookupWAnyP lookupWAny
lookupWAny : {A : Set ℓ} {B : A → Set ℓ'} {P : A → Set ℓ''} {w : W A B} → WAny P w → Σ A P
lookupWAny (here p   ) = _ , p
lookupWAny (there b i) = lookupWAny i

lookupWAnyT : FoldT lookupWAnyP
lookupWAnyT _ _ = lookupWAny

lookupWAnyC = genFoldC lookupWAnyP lookupWAnyT
