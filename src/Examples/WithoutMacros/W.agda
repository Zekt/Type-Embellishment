{-# OPTIONS --safe --with-K #-}

module Examples.WithoutMacros.W where

open import Prelude hiding (lookupAny)

open import Generics.Description
open import Generics.Recursion
open import Generics.Reflection

open import Generics.RecursionScheme
open import Generics.SimpleContainer
open import Generics.SimpleContainer.Any

data W (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  sup : (a : A) → (B a → W A B) → W A B

instance
  WC : Named (quote W) _
  unNamed WC = genDataC WD (genDataT WD W)
    where WD = genDataD W

--------
-- Transfinite induction

private
  indWP : IndP
  indWP = ind-operator (quote W)

-- unquoteDecl indW = defineInd indWP indW
indW : ∀ {ℓ'' ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} (P : W A B → Set ℓ'')
     → ((a : A) (ws : B a → W A B) → ((b : B a) → P (ws b)) → P (sup a ws))
     → (w : W A B) → P w
indW P s (sup a ws) = s a ws (λ b → indW P s (ws b))

instance indWC = genIndC indWP indW

--------
-- Any predicate

instance
  WS : SCᵈ (findDataD (quote W))
  WS = record
    { El  = λ (A , _) → A
    ; pos = (true ∷ tt ∷ []) ∷ []
    ; coe = λ _ → (refl ,ωω λ _ → lift tt) ,ωω lift tt }

private
  WAnyD : DataD
  WAnyD = AnyD (quote W)

-- unquoteDecl data WAny constructor c0 c1 = defineByDataD WAnyD WAny (c0 ∷ c1 ∷ [])
data WAny {ℓ'' ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} (P : A → Set ℓ'') :
  W A B → Set (ℓ ⊔ ℓ' ⊔ ℓ'') where
  here  : ∀ {a ws} → P a → WAny P (sup a ws)
  there : ∀ {a ws} (b : B a) → WAny P (ws b) → WAny P (sup a ws)

instance
  WAnyC : Named (quote WAny) _
  unNamed WAnyC = genDataC WAnyD WAnyT where WAnyT = genDataT WAnyD WAny

private
  lookupWAnyP : FoldP
  lookupWAnyP = lookupAny (quote W)

-- unquoteDecl lookupWAny = defineFold lookupWAnyP lookupWAny
lookupWAny : ∀ {ℓ'' ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {P : A → Set ℓ''} {w : W A B}
           → WAny P w → Σ A P
lookupWAny (here p   ) = _ , p
lookupWAny (there b i) = lookupWAny i

instance lookupWAnyC = genFoldC lookupWAnyP lookupWAny
