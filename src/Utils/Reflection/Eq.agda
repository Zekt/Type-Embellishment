{-# OPTIONS --safe --without-K #-}

open import Prelude

module Utils.Reflection.Eq where

open import Agda.Builtin.Reflection
open import Utils.Reflection.Core

private variable
  A : Set _

instance
  EqVisibility : Eq Visibility
  _==_ ⦃ EqVisibility ⦄ visible   visible   = true
  _==_ ⦃ EqVisibility ⦄ hidden    hidden    = true
  _==_ ⦃ EqVisibility ⦄ instance′ instance′ = true
  _==_ ⦃ EqVisibility ⦄ _         _         = false

  EqRelevance : Eq Relevance
  _==_ ⦃ EqRelevance ⦄ relevant   relevant   = true
  _==_ ⦃ EqRelevance ⦄ irrelevant irrelevant = true
  _==_ ⦃ EqRelevance ⦄ _          _          = false

  EqQuantity : Eq Quantity
  _==_ ⦃ EqQuantity ⦄ quantity-0 quantity-0 = true
  _==_ ⦃ EqQuantity ⦄ quantity-ω quantity-ω = true
  _==_ ⦃ EqQuantity ⦄ _          _          = false
  
  EqName : Eq Name
  _==_ {{EqName}} = primQNameEquality

  EqMeta : Eq Meta
  _==_ ⦃ EqMeta ⦄ = primMetaEquality

  EqModality : Eq Modality
  _==_ ⦃ EqModality ⦄ (modality r q) (modality r₁ q₁)
    = (r == r₁) ∧ (q == q₁)

  EqArgInfo : Eq ArgInfo
  _==_ ⦃ EqArgInfo ⦄ (arg-info v r) (arg-info v₁ r₁) =
    (v == v₁) ∧ (r == r₁)

  EqArg : ⦃ EqA : Eq A ⦄ → Eq (Arg A)
  _==_ ⦃ EqArg ⦄ (arg i x) (arg i₁ x₁) =
    (i == i₁) ∧ (x == x₁)

  EqAbs : ⦃ EqA : Eq A ⦄ → Eq (Abs A)
  _==_ ⦃ EqAbs ⦄ (abs s x) (abs s₁ x₁) = (s == s₁) ∧ (x == x₁)

  EqLiteral : Eq Literal
  _==_ ⦃ EqLiteral ⦄ (nat n)    (nat m)    = n == m 
  _==_ ⦃ EqLiteral ⦄ (word64 n) (word64 m) = n == m
  _==_ ⦃ EqLiteral ⦄ (float x)  (float y)  = x == y
  _==_ ⦃ EqLiteral ⦄ (char c)   (char d)   = c == d
  _==_ ⦃ EqLiteral ⦄ (string s) (string t) = s == t
  _==_ ⦃ EqLiteral ⦄ (name x)   (name y)   = x == y
  _==_ ⦃ EqLiteral ⦄ (meta x)   (meta y)   = x == y
  _==_ ⦃ EqLiteral ⦄ _          _          = false

eqTerm   : (x y : Term)    → Bool
eqPat    : (x y : Pattern) → Bool
eqSort   : (x y : Sort)    → Bool
eqClause : (x y : Clause)  → Bool

  
eqArgTerm : (x y : Arg Term) → Bool
eqArgTerm (arg i x) (arg i₁ x₁) = (i == i₁) ∧ eqTerm x x₁

eqAbsTerm : (x y : Abs Term) → Bool
eqAbsTerm (abs s x) (abs s₁ x₁) = (s == s₁) ∧ eqTerm x x₁

eqTel    : (x y : Telescope) → Bool
eqTel []       []       = true
eqTel ((x , a) ∷ xs) ((y , b) ∷ ys) = (x == y) ∧ eqArgTerm a b ∧ eqTel xs ys
eqTel _        _        = false

eqArgPat : (x y : Arg Pattern) → Bool
eqArgPat (arg i x) (arg i₁ x₁) = (i == i₁) ∧ eqPat x x₁

eqArgs : (x y : Args Term) → Bool
eqArgs []       []       = true
eqArgs (x ∷ xs) (y ∷ ys) = eqArgTerm x y ∧ eqArgs xs ys
eqArgs _        _        = false

eqPats : (x y : Args Pattern) → Bool
eqPats []       []       = true
eqPats (x ∷ xs) (y ∷ ys) = eqArgPat x y ∧ eqPats xs ys
eqPats _        _        = false

eqClauses : (x y : Clauses) → Bool
eqClauses []       []       = true
eqClauses (x ∷ xs) (y ∷ ys) = eqClause x y ∧ eqClauses xs ys
eqClauses _        _        = false

eqTerm (var x args)      (var x₁ args₁)      = (x == x₁) ∧ eqArgs args args₁
eqTerm (con c args)      (con c₁ args₁)      = (c == c₁) ∧ eqArgs args args₁
eqTerm (def f args)      (def f₁ args₁)      = (f == f₁) ∧ eqArgs args args₁
eqTerm (lam v t)         (lam v₁ t₁)         = (v == v₁) ∧ eqAbsTerm t t₁
eqTerm (pat-lam cs args) (pat-lam cs₁ args₁) = eqClauses cs cs₁ ∧ eqArgs args args₁
eqTerm (pi a b)          (pi a₁ b₁)          = eqArgTerm a a₁ ∧ eqAbsTerm b b₁
eqTerm (agda-sort s)     (agda-sort s₁)      = eqSort s s₁
eqTerm (lit l)           (lit l₁)            = l == l₁
eqTerm (meta x args)     (meta x₁ args₁)     = (x == x₁) ∧ eqArgs args args₁
eqTerm unknown           unknown             = true
eqTerm _                 _                   = false

eqSort (set t)     (set t₁)     = eqTerm t t₁
eqSort (lit n)     (lit n₁)     = n == n₁
eqSort (prop t)    (prop t₁)    = eqTerm t t₁
eqSort (propLit n) (propLit n₁) = n == n₁
eqSort (inf n)     (inf n₁)     = n == n₁
eqSort unknown     unknown      = true
eqSort _           _            = false

eqPat (con c ps) (con c₁ ps₁) = (c == c₁) ∧ eqPats ps ps₁
eqPat (dot t)    (dot t₁)     = eqTerm t t₁
eqPat (var x)    (var x₁)     = x == x₁
eqPat (lit l)    (lit l₁)     = l == l₁
eqPat (proj f)   (proj f₁)    = f == f₁
eqPat (absurd x) (absurd x₁)  = x == x₁
eqPat _          _            = false

eqClause (clause tel ps t)      (clause tel₁ ps₁ t₁)     = eqTel tel tel₁ ∧ eqPats ps ps₁ ∧ eqTerm t t₁
eqClause (absurd-clause tel ps) (absurd-clause tel₁ ps₁) = eqTel tel tel₁ ∧ eqPats ps ps₁
eqClause _                      _                        = false

instance
  EqTerm : Eq Term
  _==_ ⦃ EqTerm ⦄ = eqTerm
  
  EqPattern : Eq Pattern
  _==_ ⦃ EqPattern ⦄ = eqPat

  EqSort : Eq Sort
  _==_ ⦃ EqSort ⦄ = eqSort

  EqClause : Eq Clause
  _==_ ⦃ EqClause ⦄ = eqClause
