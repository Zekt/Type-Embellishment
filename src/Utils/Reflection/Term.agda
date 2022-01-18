{-# OPTIONS --safe --without-K #-}
open import Prelude

module Utils.Reflection.Term where

open import Utils.Reflection.Core
open import Utils.Reflection.Eq

------------------------------------------------------------------------
-- Context representation

-- Track both number of variables and actual context, to avoid having to
-- compute the length of the context everytime it's needed.
record Cxt : Set where
  constructor _,_
  pattern
  field
    len     : ℕ
    context : List (String × Arg Term)

private
  _∷cxt_ : String × Arg Term → Cxt → Cxt
  e ∷cxt (n , Γ) = (suc n , e ∷ Γ)

  _++cxt_ : List (String × Arg Term) → Cxt → Cxt
  es ++cxt (n , Γ) = (length es + n , es <> Γ)

-- A very limited travasal on terms
Action : Set → Set
Action A = Cxt → A → A

-- A traversal gets to operate on variables, metas, and names.
record Actions : Set where
  field
    onVar  : Action ℕ
    onMeta : Action Meta
    onCon  : Action Name
    onDef  : Action Name

defaultActions : Actions
defaultActions .Actions.onVar  _ = id
defaultActions .Actions.onMeta _ = id
defaultActions .Actions.onCon  _ = id
defaultActions .Actions.onDef  _ = id

module _ (actions : Actions) where
  open Actions actions
  traverseTerm    : Action Term
  traverseSort    : Action Sort
  traversePattern : Action Pattern
  traverseArgs    : Action (List (Arg Term))
  traverseArg     : Action (Arg Term)
  traversePats    : Action (List (Arg Pattern))
  traverseAbs     : Arg Term → Action (Abs Term)
  traverseClauses : Action Clauses
  traverseClause  : Action Clause
  traverseTel     : Action (List (String × Arg Term))

  traverseTerm Γ (var x args) = var (onVar Γ x) (traverseArgs Γ args)
  traverseTerm Γ (con c args) = con (onCon Γ c) (traverseArgs Γ args)
  traverseTerm Γ (def f args) = def (onDef Γ f) (traverseArgs Γ args)
  traverseTerm Γ (lam v t) = lam v (traverseAbs (arg (arg-info v (modality relevant quantity-ω)) unknown) Γ t)
  traverseTerm Γ (pat-lam cs args) = pat-lam (traverseClauses Γ cs) (traverseArgs Γ args)
  traverseTerm Γ (pi a b) = pi (traverseArg Γ a) (traverseAbs a Γ b)
  traverseTerm Γ (agda-sort s) = agda-sort (traverseSort Γ s)
  traverseTerm Γ (meta x args) = meta (onMeta Γ x) (traverseArgs Γ args)
  traverseTerm Γ t@(lit l) = t
  traverseTerm Γ t@unknown = t

  traverseSort Γ (set t) = set (traverseTerm Γ t)
  traverseSort Γ (prop t) = prop (traverseTerm Γ t)
  traverseSort Γ t = t

  traversePattern Γ (con c ps) = con (onCon Γ c) (traversePats Γ ps)
  traversePattern Γ (dot t) = dot (traverseTerm Γ t)
  traversePattern Γ (var x) = var (onVar Γ x)
  traversePattern Γ (absurd x) = absurd (onVar Γ x)
  traversePattern Γ t = t
  traversePats Γ [] = []
  traversePats Γ ((arg i p) ∷ pats) = arg i (traversePattern Γ p) ∷ traversePats Γ pats

  traverseArg Γ (arg i x) = arg i (traverseTerm Γ x)
  traverseArgs Γ [] = []
  traverseArgs Γ (x ∷ args) = traverseArg Γ x ∷ traverseArgs Γ args

  traverseAbs ty Γ (abs x t) = abs x (traverseTerm ((x , ty) ∷cxt Γ) t)

  traverseClause Γ (clause tel ps t) =
    clause (traverseTel Γ tel)
           (traversePats (reverse tel ++cxt Γ) ps)
           (traverseTerm (reverse tel ++cxt Γ) t)
  traverseClause Γ (absurd-clause tel ps) =
    absurd-clause (traverseTel Γ tel)
                  (traversePats (reverse tel ++cxt Γ) ps)
  traverseClauses Γ [] = []
  traverseClauses Γ (x ∷ cls) = traverseClause Γ x ∷ traverseClauses Γ cls

  traverseTel Γ [] = []
  traverseTel Γ ((s , t) ∷ tel) = (s , traverseArg Γ t) ∷ traverseTel ((s , t) ∷cxt Γ) tel

weaken : ℕ → ℕ → Term → Term
weaken from by = traverseTerm (record defaultActions
                                      {onVar = λ Γ x →
                                         if x <? (Cxt.len Γ + from)
                                           then x
                                           else x + by}) (0 , [])

weakenTel : ℕ → ℕ → Telescope → Telescope
weakenTel from by [] = []
weakenTel from by (x ∷ tel) = bimap id (fmap (weaken from by)) x ∷
                              weakenTel (suc from) by tel

strengthen : ℕ → ℕ → Term → Term
strengthen from by = traverseTerm (record defaultActions
                                      {onVar = λ Γ x →
                                         if x <? (Cxt.len Γ + from)
                                           then x
                                           else x ∸ by}) (0 , [])

prefixToType : Telescope → Type → Type
prefixToType []              `B = `B
prefixToType ((s , `A) ∷ `T) `B = `Π[ s ∶ `A ] prefixToType `T `B

prefixToTerm : Telescope → Term → Term
prefixToTerm []              `t = `t
prefixToTerm ((s , `A) ∷ `T) `t =
  lam (getVisibility `A) (abs s (prefixToTerm `T `t))

levels : ℕ → Telescope
levels zero    = []
levels (suc n) = ("ℓ" , hArg `Level) ∷ levels n

vUnknowns : ℕ → Args Term
vUnknowns = flip duplicate (vArg unknown)

hUnknowns : ℕ → Args Term
hUnknowns = flip duplicate (hArg unknown)

private
  -- Assumption: The argument is a valid type.
  ΠToTelescope : Type → Telescope × Type
  ΠToTelescope (`Π[ s ∶ a ] b) = let T , A = ΠToTelescope b in (s , a) ∷ T , A
  ΠToTelescope t               = [] , t

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

splitType : ℕ → Type → Telescope × Type
splitType zero    x               = [] , x
splitType (suc n) (`Π[ s ∶ a ] b) =
  let tel , c = splitType n b in (s , a) ∷ tel , c
splitType _       a               = [] , a

dropType : ℕ → Type → Type
dropType n = snd ∘ splitType n 

forgetTypes : Telescope → Telescope
forgetTypes = map $ bimap id (λ `A → arg (getArgInfo `A) unknown)

endsIn : Type → Name → Bool
endsIn (def f _)       u = f == u
endsIn (`Π[ _ ∶ _ ] b) u = endsIn b u
endsIn _               u = false
