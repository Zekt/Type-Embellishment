{-# OPTIONS --safe #-}
open import Prelude
  hiding ([_,_]; _++_)

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
{-  
record Code (A : Set ℓ) : Set ℓ where
  constructor _,_
  field
    val : A
    code  : Term 
open Code
-}
Types     = List Type
Clauses   = List Clause
Telescope = List (String × Arg Type)
Context   = List (Arg Type)

Args : Set ℓ → Set ℓ
Args A = List (Arg A)

Tactic = Term → TC ⊤

--- Terms ---

pattern `Set₀ = agda-sort (lit 0)
pattern `Set₁ = agda-sort (lit 1)
pattern `Set₂ = agda-sort (lit 2)

pattern `Set n = agda-sort (lit n)

pattern `Set! = agda-sort unknown

pattern `Level = def (quote Level) []

pattern relevant-ω              = modality relevant quantity-ω
pattern relevant-erased         = modality relevant quantity-0
pattern visible-relevant-ω      = arg-info visible  relevant-ω
pattern hidden-relevant-ω       = arg-info hidden   relevant-ω
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

pattern def₀ f         = def f []
pattern def₁ f x       = def f (vArg x ∷ [])
pattern def₂ f x y     = def f (vArg x ∷ vArg y ∷ [])
pattern def₃ f x y z   = def f (vArg x ∷ vArg y ∷ vArg z ∷ [])
pattern def₄ f x y z u = def f (vArg x ∷ vArg y ∷ vArg z ∷ vArg u ∷ [])

pattern vLam x = lam visible x
pattern hLam x = lam hidden x
pattern iLam x = lam instance′ x

pattern `Π[_∶_]_ s a ty  = pi a (abs s ty)
pattern `Π[_]_ a ty      = `Π[ "_" ∶ a ] ty
pattern vΠ[_∶_]_ s a ty = `Π[ s ∶ (vArg a) ] ty
pattern hΠ[_∶_]_ s a ty = `Π[ s ∶ (hArg a) ] ty
pattern iΠ[_∶_]_ s a ty = `Π[ s ∶ (iArg a) ] ty
pattern vΠ[_]_ a ty     = `Π[ vArg a ] ty
pattern hΠ[_]_ a ty     = `Π[ hArg a ] ty
pattern iΠ[_]_ a ty     = `Π[ iArg a ] ty

infixr 20 `vλ_`→_ `hλ_`→_ `iλ_`→_

`vλ_`→_ : String → Term → Term
`vλ s `→ b = vLam (abs s b)

`hλ_`→_ : String → Term → Term
`hλ s `→ b = hLam (abs s b)

`iλ_`→_ : String → Term → Term
`iλ s `→ b = iLam (abs s b)

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

private
  -- Assumption: The argument is a valid type.
  ΠToTelescope : Type → Telescope × Type
  ΠToTelescope (pi a (abs s b)) = let T , A = ΠToTelescope b in (s , a) ∷ T , A
  ΠToTelescope t                = [] , t

  TelescopeToΠ : Type → Telescope → Type
  TelescopeToΠ `B []             = `B
  TelescopeToΠ `B ((s , `A) ∷ T) = `Π[ s ∶ `A ] TelescopeToΠ `B T
instance
  TelescopeToContext : Coercion' Telescope Context
  ⇑_ ⦃ TelescopeToContext ⦄ = map snd

  TypeToTelescope : Coercion' Type (Telescope × Type)
  ⇑_ ⦃ TypeToTelescope ⦄ = ΠToTelescope

  TelescopeToType : Coercion' (Telescope × Type) Type
  ⇑_ ⦃ TelescopeToType ⦄ (T , `A) = TelescopeToΠ `A T
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

IMPOSSIBLE : Term → TC A
IMPOSSIBLE t = typeError $ termErr t ∷ [ strErr " should not occur" ]

give : Term → Tactic
give v = λ hole → unify hole v

define : Arg Name → Type → Clauses → TC ⊤
define f a cs = declareDef f a >> defineFun (unArg f) cs

define! : Type → Clauses → TC Name
define! a cs = do
  f ← freshName "_"
  define (vArg f) a cs
  return f

quoteTC! : A → TC Term
quoteTC! a = withNormalisation true (quoteTC a)

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

evalTC : ∀ {a} {A : Set a} → TC A → Tactic
evalTC {A = A} c hole = do
  v  ← c
  `v ← quoteTC v
  `A ← quoteTC A
  checkedHole ← checkType hole `A
  unify checkedHole `v

macro
  evalT : ∀ {a} {A : Set a} → TC A → Tactic
  evalT = evalTC

-- Typed version of extendContext
extendContextT : ArgInfo → (B : Set ℓ)
  → (Type → B → TC A) → TC A
extendContextT i B f = do
  `B ← quoteTC B
  extendContext (arg i `B) do
    x ← unquoteTC {A = B} (var₀ 0)
    f `B x

getDefType : Name → TC Type
getDefType n = caseM getDefinition n of λ where
    (data-cons d) → inferType $ con n []
    _             → inferType $ def n []

getTelescope : Name → TC (Telescope × Type)
getTelescope s = ⦇ ⇑ (getDefType s) ⦈

macro
  getTelescopeT : Name → Tactic
  getTelescopeT s = evalTC $ getTelescope s

prefixToType : Telescope → Type → Type
prefixToType []              `B = `B
prefixToType ((s , `A) ∷ `Γ) `B = `Π[ s ∶ `A ] prefixToType `Γ `B
