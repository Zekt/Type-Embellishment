{-# OPTIONS --safe #-}

open import Prelude
  hiding (intersperse)

module Utils.Reflection.Show where

open import Agda.Builtin.Reflection
  using (primShowQName; primShowMeta)

open import Utils.String
open import Utils.Reflection.Core

instance
  ShowName : Show Name
  show {{ShowName}} x = primShowQName x

  ShowMeta : Show Meta
  show {{ShowMeta}} = primShowMeta

  ShowRelevance : Show Relevance
  show ⦃ ShowRelevance ⦄ relevant   = "relevant"
  show ⦃ ShowRelevance ⦄ irrelevant = "irrelevant"

  showVisibility : Show Visibility
  show ⦃ showVisibility ⦄ visible   = "visible"
  show ⦃ showVisibility ⦄ hidden    = "hidden"
  show ⦃ showVisibility ⦄ instance′ = "instance"

  showLiteral : Show Literal
  show ⦃ showLiteral ⦄ (nat n)    = show n
  show ⦃ showLiteral ⦄ (word64 n) = show n
  show ⦃ showLiteral ⦄ (float x)  = show x
  show ⦃ showLiteral ⦄ (char c)   = show c
  show ⦃ showLiteral ⦄ (string s) = show s
  show ⦃ showLiteral ⦄ (name x)   = show x
  show ⦃ showLiteral ⦄ (meta x)   = show x

private
  -- add appropriate parens depending on the given visibility
  visibilityParen : Visibility → String → String
  visibilityParen visible   s = parensIfSpace s
  visibilityParen hidden    s = braces s
  visibilityParen instance′ s = braces (braces s)

mutual

  showTerms : List (Arg Term) → String
  showTerms []             = ""
  showTerms (a@(arg i t) ∷ ts) = visibilityParen (getVisibility a) (showTerm t) <+> showTerms ts

  showTerm : Term → String
  showTerm (var x args)         = "var" <+> show x <+> showTerms args
  showTerm (con c args)         = show c <+> showTerms args
  showTerm (def f args)         = show f <+> showTerms args
  showTerm (lam v (abs s x))    = "λ" <+> visibilityParen v s <+> "→" <+> showTerm x
  showTerm (pat-lam cs args)    =
    "λ {" <+> showClauses cs <+> "}" <+> showTerms args
  showTerm (pi a′@(arg i a) (abs s b)) =
    "Π (" <> visibilityParen (getVisibility a′) s <+> ":" <+>
    parensIfSpace (showTerm a) <> ")" <+> parensIfSpace (showTerm b)
  showTerm (agda-sort s)        = showSort s
  showTerm (lit l)              = show l
  showTerm (meta x args)        = show x <+> showTerms args
  showTerm unknown              = "unknown"

  showSort : Sort → String
  showSort (set t) = "Set" <+> parensIfSpace (showTerm t)
  showSort (lit n) = "Set" <> show n -- no space to disambiguate from set t
  showSort (prop t) = "Prop" <+> parensIfSpace (showTerm t)
  showSort (propLit n) = "Prop" <> show n -- no space to disambiguate from prop t
  showSort (inf n) = "Setω" <> show n
  showSort unknown = "unknown"

  showPatterns : List (Arg Pattern) → String
  showPatterns []       = ""
  showPatterns (a ∷ ps) = showArg a <+> showPatterns ps
    where
    -- Quantities are ignored.
    showArg : Arg Pattern → String
    showArg (arg (arg-info h (modality r _)) p) =
      braces? (show r <> showPattern p)
      where
      braces? = case h of λ where
        visible   → id
        hidden    → braces
        instance′ → braces ∘ braces

  showPattern : Pattern → String
  showPattern (con c []) = show c
  showPattern (con c ps) = parens (show c <+> showPatterns ps)
  showPattern (dot t)    = "." <> parens (showTerm t)
  showPattern (var x)    = "pat-var" <+> show x
  showPattern (lit l)    = show l
  showPattern (proj f)   = show f
  showPattern (absurd _) = "()"

  showClause : Clause → String
  showClause (clause tel ps t)      = "[" <+> showTel tel <+> "]" <+> showPatterns ps <+> "→" <+> showTerm t
  showClause (absurd-clause tel ps) = "[" <+> showTel tel <+> "]" <+> showPatterns ps

  showClauses : List Clause → String
  showClauses []       = ""
  showClauses (c ∷ cs) = showClause c <+> ";" <+> showClauses cs

  showTel : List (String × Arg Type) → String
  showTel [] = ""
  showTel ((x , a@(arg i t)) ∷ tel) =
    visibilityParen (getVisibility a) (x <+> ":" <+> showTerm t) <> showTel tel

instance
  ShowTerm : Show Term
  show ⦃ ShowTerm ⦄ = showTerm
  
  ShowSort : Show Sort
  show ⦃ ShowSort ⦄ = showSort

  ShowPattern : Show Pattern
  show ⦃ ShowPattern ⦄ = showPattern

  ShowClause : Show Clause
  show ⦃ ShowClause ⦄ = showClause
  
showDefinition : Definition → String
showDefinition (function cs)       = "function" <+> braces (showClauses cs)
showDefinition (data-type pars cs) =
 "datatype" <+> show pars <+> braces (intersperse ", " (fmap show cs))
showDefinition (record-type c fs)  = "record" <+> show c <+> braces (intersperse ", " (fmap (show ∘ unArg) fs))
showDefinition (data-cons d)       = "constructor" <+> show d
showDefinition axiom               = "axiom"
showDefinition prim-fun            = "primitive"

instance
  ShowDefinition : Show Definition
  show ⦃ ShowDefinition ⦄ = showDefinition
