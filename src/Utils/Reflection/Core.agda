{-# OPTIONS --safe --without-K #-}
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

Names      = List Name
Terms      = List Term
Types      = List Type
Clauses    = List Clause
Context    = List (Arg Type)
ErrorParts = List ErrorPart

Args : Set ℓ → Set ℓ
Args A = List (Arg A)

Tactic = Term → TC ⊤

--- Terms ---

pattern `Set₀  = agda-sort (lit 0)
pattern `Set₁  = agda-sort (lit 1)
pattern `Set₂  = agda-sort (lit 2)
pattern `Set n = agda-sort (lit n)
pattern `Set?  = agda-sort unknown

pattern relevant-ω              = modality relevant quantity-ω
pattern visible-relevant-ω      = arg-info visible  relevant-ω
pattern hidden-relevant-ω       = arg-info hidden   relevant-ω

pattern relevant-erased         = modality relevant quantity-0
pattern visible-relevant-erased = arg-info visible  relevant-erased
pattern hidden-relevant-erased  = arg-info hidden   relevant-erased

pattern vArg x = arg (arg-info visible relevant-ω) x
pattern hArg x = arg (arg-info hidden  relevant-ω) x
pattern iArg x = arg (arg-info instance′ relevant-ω) x

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
pattern con₅ c x y z u v = con c (vArg x ∷ vArg y ∷ vArg z ∷ vArg u ∷ vArg v ∷ [])

pattern def₀ f         = def f []
pattern def₁ f x       = def f (vArg x ∷ [])
pattern def₂ f x y     = def f (vArg x ∷ vArg y ∷ [])
pattern def₃ f x y z   = def f (vArg x ∷ vArg y ∷ vArg z ∷ [])
pattern def₄ f x y z u = def f (vArg x ∷ vArg y ∷ vArg z ∷ vArg u ∷ [])

pattern vLam x = lam visible x
pattern hLam x = lam hidden x
pattern iLam x = lam instance′ x

pattern pat-lam₀ cs = pat-lam cs []

pattern `Π[_∶_]_ s a ty  = pi a (abs s ty)
pattern `Π[_]_ a ty      = `Π[ "_" ∶ a ] ty
pattern vΠ[_∶_]_ s a ty = `Π[ s ∶ (vArg a) ] ty
pattern hΠ[_∶_]_ s a ty = `Π[ s ∶ (hArg a) ] ty
pattern iΠ[_∶_]_ s a ty = `Π[ s ∶ (iArg a) ] ty
pattern vΠ[_]_ a ty     = `Π[ vArg a ] ty
pattern hΠ[_]_ a ty     = `Π[ hArg a ] ty
pattern iΠ[_]_ a ty     = `Π[ iArg a ] ty

pattern _⊢_`=_ tel ps t = clause tel ps t 

pattern `lzero   = def₀ (quote lzero)
pattern `Level   = def₀ (quote Level)
pattern `tt      = con₀ (quote tt)
pattern _`,_ t u = con₂ (quote Prelude._,_) t u

infixr 20 `vλ_`→_ `hλ_`→_ `iλ_`→_

pattern `vλ_`→_ s b = vLam (abs s b)
pattern `hλ_`→_ s b = hLam (abs s b)
pattern `iλ_`→_ s b = iLam (abs s b)

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

mapArgs : (A → B) → Args A → Args B
mapArgs f []       = []
mapArgs f (x ∷ xs) = fmap f x ∷ mapArgs f xs

instance
  ArgsFunctor : Functor λ A → List (Arg A)
  fmap ⦃ ArgsFunctor ⦄ = mapArgs

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

