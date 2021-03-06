{-# OPTIONS --safe --without-K #-}
open import Prelude renaming (Any to AnyL)

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

Finder : Set → Set
Finder A = Cxt → A → Bool

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

anyVisibleTerm : (Cxt → Term → Bool) → Cxt → Term → Bool
anyVisibleTerm f Γ t = if f Γ t then true else
  case t of λ where
    (var _ args) → any visibleTrue args
    (con _ args) → any visibleTrue args
    (def _ args) → any visibleTrue args
    (lam v (abs s x)) → anyVisibleTerm f ((s , arg (arg-info v (modality relevant quantity-ω)) unknown) ∷cxt Γ) x
    (pat-lam cs args) → any visibleTrue args
    (`Π[ s ∶ arg i x ] y) → anyVisibleTerm f Γ x ∨ anyVisibleTerm f ((s , arg i x) ∷cxt Γ) y
    (meta _ xs) → any visibleTrue xs
    _ → false
  where visibleTrue : (Arg _) → Bool
        visibleTrue a = isVisible a ∧ f Γ (unArg a)

anyTerm : (Cxt → Term → Bool) → Cxt → Term → Bool
anyTerm f Γ t = if f Γ t then true
              else case t of λ where
                (var _ args) → any (f Γ ∘ unArg) args
                (con _ args) → any (f Γ ∘ unArg) args
                (def _ args) → any (f Γ ∘ unArg) args
                (lam v (abs s x)) → anyTerm f ((s , arg (arg-info v (modality relevant quantity-ω)) unknown) ∷cxt Γ) x
                (pat-lam cs args) → any (f Γ ∘ unArg) args
                (`Π[ s ∶ arg i x ] y) → anyTerm f Γ x ∨ anyTerm f ((s , arg i x) ∷cxt Γ) y
                (meta _ xs) → any (f Γ ∘ unArg) xs
                _ → false

anyPat : (Pattern → Bool) → Pattern → Bool
anyPat f p = if (f p) then true
             else case p of λ where
               (con c ps) → any (f ∘ unArg) ps
               _ → false

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

prependToType : Telescope → Type → Type
prependToType []              `B = `B
prependToType ((s , `A) ∷ `T) `B = `Π[ s ∶ `A ] prependToType `T `B

prependToTerm : Telescope → Term → Term
prependToTerm []              `t = `t
prependToTerm ((s , `A) ∷ `T) `t =
  lam (getVisibility `A) (abs s (prependToTerm `T `t))
                              
`Levels : ℕ → Telescope
`Levels n = duplicate n ("ℓ" , hArg `Level)

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


-- renaming types
unConflictType : Type → Type
unConflictType t = unconflict [] t
  where
    mostElem : String → ℕ → List (String × ℕ)
              → ℕ × (List (String × ℕ))
    mostElem x n [] = n ,  [ (x , n) ]
    mostElem x m ((s , n) ∷ ss) =
      if x == s then
        if m ≤? n then
          (suc n) , (s , suc n) ∷ ss
        else
          (m , (s , m) ∷ ss)
      else
        let n' , ss' = mostElem x m ss
        in  n' , (s , n) ∷ ss'

    unconflict : List (String × ℕ) → Type → Type
    unconflict ss (`Π[ s ∶ a ] x) =
      let cs       = ⇑ s
          cs'      = removeLast (lenTrailingNat cs) cs
          n , ss' = mostElem (⇑ cs') (fromMaybe 0 (trailingNat cs)) ss
          ns = if n == 0 then "" else show n
        in `Π[ ⇑ cs' <> ns ∶ a ] unconflict ss' x
    unconflict _ t = t

renameTypeBy : Type → List String → Type
renameTypeBy (`Π[ _ ∶ a ] x) (s ∷ ss) = `Π[ s ∶ a ] (renameTypeBy x ss)
renameTypeBy t _ = t

renameTelBy : Telescope → List String → Telescope
renameTelBy ((_ , x) ∷ tel) (s ∷ ss) = (s , x) ∷ renameTelBy tel ss
renameTelBy tel _ = tel
