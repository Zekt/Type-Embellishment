{-# OPTIONS --safe #-}
open import Prelude

module Utils.Reflection.Core where
open import Agda.Builtin.Reflection as Builtin
open Builtin public
  hiding ( primQNameEquality
         ; primQNameLess
         ; primShowQName
         ; primMetaEquality
         ; primMetaLess
         ; primShowMeta )

private variable
  A B : Set _

-- Types
  
Clauses   = List Clause
Telescope = List (String × Arg Type)

Args : Set ℓ → Set ℓ
Args A = List (Arg A)

Tactic = Term → TC ⊤

--- Terms ---

pattern `Set₀ = agda-sort (lit 0)
pattern `Set₁ = agda-sort (lit 1)
pattern `Set₂ = agda-sort (lit 2)

pattern `Set! = agda-sort unknown

pattern default-modality = modality relevant quantity-ω

pattern vArg x = arg (arg-info visible default-modality) x
pattern hArg x = arg (arg-info hidden default-modality) x
pattern iArg x = arg (arg-info instance′ default-modality) x

pattern var₀ x         = var x []
pattern var₁ x a       = var x (vArg a ∷ [])
pattern var₂ x a b     = var x (vArg a ∷ vArg b ∷ [])
pattern var₃ x a b c   = var x (vArg a ∷ vArg b ∷ vArg c ∷ [])
pattern var₄ x a b c d = var x (vArg a ∷ vArg b ∷ vArg c ∷ vArg d ∷ [])

pattern con₀ c         = con c []
pattern con₁ c x       = con c (vArg x ∷ [])
pattern con₂ c x y     = con c (vArg x ∷ vArg y ∷ [])
pattern con₃ c x y z   = con c (vArg x ∷ vArg y ∷ vArg z ∷ [])
pattern con₄ c x y z u = con c (vArg x ∷ vArg y ∷ vArg z ∷ vArg u ∷ [])

pattern def₀ f         = def f []
pattern def₁ f x       = def f (vArg x ∷ [])
pattern def₂ f x y     = def f (vArg x ∷ vArg y ∷ [])
pattern def₃ f x y z   = def f (vArg x ∷ vArg y ∷ vArg z ∷ [])
pattern def₄ f x y z u = def f (vArg x ∷ vArg y ∷ vArg z ∷ vArg u ∷ [])

pattern vLam x = lam visible x
pattern hLam x = lam hidden x
pattern iLam x = lam instance′ x

unArg : Arg A → A
unArg (arg _ x) = x

getArgInfo : Arg A → ArgInfo
getArgInfo (arg i _) = i

getVisibility : Arg A → Visibility
getVisibility (arg (arg-info v _) _) = v

getModality : Arg A → Modality
getModality (arg (arg-info _ m) _) = m

getRelevance : Arg A → Relevance
getRelevance (arg (arg-info _ (modality r _)) _) = r

getQuantity : Arg A → Quantity
getQuantity (arg (arg-info _ (modality _ q)) _) = q

isVisible : Arg A → Bool
isVisible (arg (arg-info visible _) _) = true
isVisible _ = false

instance
  FunctorArg : Functor Arg
  fmap {{FunctorArg}} f (arg i x) = arg i (f x)

  ArgsFunctor : Functor λ A → List (Arg A)
  fmap ⦃ ArgsFunctor ⦄ f []       = []
  fmap ⦃ ArgsFunctor ⦄ f (x ∷ xs) = fmap f x ∷ fmap f xs

unAbs : Abs A → A
unAbs (abs _ x) = x

instance
  FunctorAbs : Functor Abs
  fmap {{FunctorAbs}} f (abs s x) = abs s (f x)

absurd-lam : Term
absurd-lam = pat-lam (absurd-clause (("()" , vArg unknown) ∷ []) (vArg (absurd 0) ∷ []) ∷ []) []

--- TC monad ---

mapTC : (A → B) → TC A → TC B
mapTC f m = bindTC m λ x → returnTC (f x)

instance
  FunctorTC : Functor TC
  fmap ⦃ FunctorTC ⦄ = mapTC

  ApplicativeTC : Applicative TC
  pure  ⦃ ApplicativeTC ⦄ = returnTC
  _<*>_ ⦃ ApplicativeTC ⦄ = monadAp bindTC

  MonadTC : Monad TC
  _>>=_  ⦃ MonadTC ⦄ = bindTC

  FunctorZeroTC : FunctorZero TC
  empty ⦃ FunctorZeroTC ⦄ = typeError []

  AlternativeTC : Alternative TC
  _<|>_ ⦃ AlternativeTC ⦄ = catchTC


give : Term → Tactic
give v = λ hole → unify hole v

define : Arg Name → Type → List Clause → TC ⊤
define f a cs = declareDef f a >> defineFun (unArg f) cs

newMeta : Type → TC Term
newMeta = checkType unknown

newMeta! : TC Term
newMeta! = newMeta unknown

typeErrorS : String → TC A
typeErrorS s = typeError (strErr s ∷ [])

blockOnMeta! : Meta → TC A
blockOnMeta! x = commitTC >>= λ _ → blockOnMeta x

inferNormalisedType : Term → TC Type
inferNormalisedType t = withNormalisation true (inferType t)

