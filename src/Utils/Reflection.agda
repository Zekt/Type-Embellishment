{-# OPTIONS --safe --without-K #-}
open import Prelude
  hiding ([_,_])

module Utils.Reflection where

open import Utils.Reflection.Core     public
open import Utils.Reflection.Eq       public
open import Utils.Reflection.Show     public
open import Utils.Reflection.Term     public

private variable
  A : Set ℓ

IMPOSSIBLE : TC A
IMPOSSIBLE = typeError $ [ strErr "An impossible event occurs." ]

IMPOSSIBLE-term : Term → TC A
IMPOSSIBLE-term t = typeError $ termErr t ∷ [ strErr " should not occur" ]

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

getFunction : Name → TC (Type × Clauses)
getFunction s = do
  function cs ← getDefinition s
    where t → typeError $ [ strErr (show s <> " is not a function.") ]
  t ← getType s
  return $ t , cs
  
getTelescope : Name → TC (Telescope × Type)
getTelescope s = ⦇ ⇑ (getDefType s) ⦈

macro
  getTelescopeT : Name → Tactic
  getTelescopeT s = evalTC $ getTelescope s

getLevel : Type → TC Level
getLevel t = case t of λ where
               (def₀ (quote Set))       → return lzero
               (def  (quote Set) [ l ]) → unquoteTC (unArg l)
               _ → typeError (termErr t
                             ∷ strErr "is not a type."
                             ∷ [])
