{-# OPTIONS --safe --without-K #-}
open import Prelude
  hiding ([_,_])

module Utils.Reflection.Tactic where

open import Utils.Reflection.Core
open import Utils.Reflection.Show
open import Utils.Reflection.Term
import Utils.Error as Err

private variable
  A : Set ℓ

dprint = debugPrint "meta" 5

give : Term → Tactic
give v = λ hole → unify hole v

define : Arg Name → Type → Clauses → TC ⊤
define f a cs = declareDef f a >> defineFun (unArg f) cs

define! : Type → Clauses → TC Name
define! a cs = do
  f ← freshName "_"
  define (vArg f) a cs
  return f

extend*Context : Telescope → TC A → TC A
extend*Context []              m = m
extend*Context ((s , a) ∷ tel) m = extendContext s a (extend*Context tel m)

quoteTC! : A → TC Term
quoteTC! a = withNormalisation true (quoteTC a)

quoteωTC! : {A : Setω} → A → TC Term
quoteωTC! a = withNormalisation true (quoteωTC a)

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

formatErrorPart : ErrorPart → TC String
formatErrorPart = formatErrorParts ∘ [_]

evalTC : TC A → Tactic
evalTC {A = A} c hole = do
  v  ← c
  `v ← quoteTC v
  `A ← quoteTC A
  checkedHole ← checkType hole `A
  unify checkedHole `v

macro
  evalT : TC A → Tactic
  evalT = evalTC

-- Typed version of extendContext
extendContextT : String → ArgInfo → (B : Set ℓ)
  → (Type → B → TC A) → TC A
extendContextT s i B f = do
  `B ← quoteTC! B
  extendContext s (arg i `B) do
    x ← unquoteTC {A = B} (var₀ 0)
    f `B x

getConTelescope : Name → (pars : ℕ) → TC Telescope
getConTelescope c pars = drop pars ∘ fst ∘ (coerce'_to (Telescope × Type)) <$> getType c

getAbsName : {A : Set ℓ} {B : A → Set ℓ′} → ((x : A) → B x) → TC String
getAbsName f = caseM quoteTC! f of λ { (lam visible (abs s _)) → return s ; t → Err.notλ t }

getAbsNameω : {A : Set ℓ} {B : A → Setω} → ((x : A) → B x) → TC String
getAbsNameω f = caseM quoteωTC! f of λ { (lam visible (abs s _)) → return s ; t → Err.notλ t }

getFunction : Name → TC (Type × Clauses)
getFunction d = do
  function cs ← getDefinition d
    where t → Err.notFun d
  t ← getType d
  return $ t , cs

getDataDefinition : Name → TC (ℕ × Names)
getDataDefinition d = do
  data-type pars cs ← getDefinition d
    where _ → Err.notData (def₀ d)
  return $ pars , cs

getTelescope : Name → TC (Telescope × Type)
getTelescope s = ⦇ ⇑ (getType s) ⦈

macro
  getTelescopeT : Name → Tactic
  getTelescopeT s = evalTC $ getTelescope s

getSetLevel : Type → TC Term
getSetLevel (agda-sort (set t)) = return t
getSetLevel (`Set n) = quoteTC (fromℕ n)
  where 
    fromℕ : ℕ → Level
    fromℕ zero = lzero
    fromℕ (suc n) = lsuc (fromℕ n)
getSetLevel (def (quote Set) []) = return (quoteTerm lzero)
getSetLevel (def (quote Set) [ arg _ x ]) = return x
getSetLevel t = quoteTC t >>= λ t →
                  typeError [ strErr $ showTerm t <> " level error!" ]


-- Rename names in a telescope to the first letter of the given type,
-- if no name is given
renameUnderscore : Telescope → TC Telescope
renameUnderscore []        = return []
renameUnderscore (("_" , x@(arg visible-relevant-ω `A)) ∷ as) = do
  s ← formatErrorPart $ termErr `A
  -- let s = ⇑ [ maybe′ toLower 'x' $ head (⇑ s ⦂ List Char) ]
  extendContext s x $ (("x" , x) ∷_) <$> renameUnderscore as
renameUnderscore (a@(s , x) ∷ as) = extendContext s x $ a ∷_ <$> renameUnderscore as
