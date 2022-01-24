{-# OPTIONS --safe --without-K #-}
open import Prelude

module Utils.Reflection.Print where

open import Utils.Reflection.Core
open import Utils.Reflection.Term
open import Utils.Reflection.Eq
open import Utils.Reflection.Tactic

infoName = "print"
verbosity = 5

  
private
  variable
    A : Set _

  pattern space     = strErr " "
  pattern colon     = strErr " : "
  

paren : Visibility → ErrorParts → ErrorParts
paren v s = case v of λ where
  visible   → [ strErr "(" ] <> s <> [ strErr ")" ]
  hidden    → [ strErr "{" ] <> s <> [ strErr "}" ]
  instance′ → [ strErr "⦃ "] <> s <> [ strErr " ⦄"]
  
sep : ErrorParts → ErrorParts
sep []       = []
sep (e ∷ []) = e ∷ []
sep (e ∷ es) = e ∷ space ∷ sep es

record ToErr (A : Set) : Set₀ where
  field
    toErr : A → ErrorParts
open ToErr ⦃...⦄ public

instance 
  ArgErr : ⦃ _ : ToErr A ⦄ → ToErr (Arg A)
  ArgErr .toErr a = paren (getVisibility a) (toErr (unArg a)) 

instance
  ListErr : ⦃ _ : ToErr A ⦄ → ToErr (List A)
  ListErr .toErr = sep ∘ concatMap toErr

  TermErr : ToErr Term
  TermErr .toErr = [_] ∘ termErr
  
  PattErr : ToErr Pattern
  PattErr .toErr = [_] ∘ pattErr

  NameErr : ToErr Name
  NameErr .toErr = [_] ∘ nameErr

  StrErr  : ToErr String
  StrErr .toErr = [_] ∘ strErr

{-
mutual 
  pattErr : Pattern → ErrorParts
  pattErr (con c ps) = nameErr c ∷ pattsErr ps
  pattErr (dot t)    = strErr "." ∷ termErr t ∷ []
  pattErr (var x)    = termErr (var₀ x) ∷ []
  pattErr (lit l)    = termErr (lit l) ∷ []
  pattErr (proj f)   = strErr "." ∷ nameErr f ∷ []
  pattErr (absurd x) = strErr "()" ∷ []

  pattsErr : Args Pattern → ErrorParts
  pattsErr []                            = []
  pattsErr ((arg (arg-info v _) a) ∷ []) = pattErr a
  pattsErr ((arg (arg-info v _) a) ∷ as) = pattErr a
    <> (space ∷ pattsErr as)

instance
  PattErr : ToErr Pattern
  PattErr .toErr = pattErr
-}
vcat : List String → String
vcat []           = ""
vcat (msg ∷ [])   = msg 
vcat (msg ∷ msgs) = msg <> "\n" <> vcat msgs 

nest : List String → List String
nest = map ("  " <>_) 

mergeSpace : ErrorParts → ErrorParts
mergeSpace []                     = []
mergeSpace (space ∷ space ∷ msg)  = mergeSpace (space ∷ msg)
mergeSpace (err   ∷ errs)         = err ∷ mergeSpace errs

printArg : (showImplicit : Bool) → Arg A → (A → TC ErrorParts) → TC ErrorParts
printArg b x f = case getVisibility x of λ where
  visible → do
    err ← f (unArg x)
    return $ if elem space err
      then paren visible err
      else err
  v → if b
    then (paren v <$> f (unArg x))
    else return []
  
printTelescope : Telescope → TC ErrorParts → TC ErrorParts
printTelescope []             m = m
printTelescope ((s , x) ∷ []) m = do
  ss ← extendContext s x m
  s  ← extendContext s x (formatErrorParts $ toErr (var₀ 0))
  ts ← formatErrorParts $ toErr $ unArg x
  return $ paren (getVisibility x) (toErr s <> colon ∷ toErr ts) <> ss
printTelescope ((s , x) ∷ tel) m = do
  ss ← extendContext s x $ printTelescope tel m
  s  ← extendContext s x (formatErrorParts $ toErr (var₀ 0))
  ts ← formatErrorParts $ toErr $ unArg x
  return $ paren (getVisibility x) (toErr s <> space ∷ toErr ":" <> space ∷ toErr ts) <> space ∷ ss

printDataSignature : (tel : Telescope) → Type → TC ErrorParts
printDataSignature tel a = printTelescope tel do
    a ← formatErrorParts $ toErr a
    return $ space ∷ toErr ":" <> space ∷ toErr a

printCon : (pars : ℕ) → (c : Name) → TC String
printCon pars c = do
  x ← getType c
  let a = snd $ splitType pars x
  formatErrorParts $ nameErr c ∷ space ∷ strErr ":" ∷ space ∷ termErr a ∷ []

printCons : (pars : ℕ) → (cs : Names) → TC (List String)
printCons pars = mapM (printCon pars)

printData : Name → TC ⊤
printData d = do
  pars , cs ← getDataDefinition d
  x ← getType d
  let tel , a = splitType pars x

  sig  ← printDataSignature tel a
  decl ← formatErrorParts $ mergeSpace $
    strErr "data" ∷ space ∷ nameErr d ∷ space ∷ [] <> sig <> space ∷ strErr "where" ∷ []

  cons ← vcat ∘ nest <$> extend*Context tel (printCons pars cs)
  debugPrint infoName verbosity $ [ strErr (vcat $ decl ∷ cons ∷ []) ]

printConAs : (String × Type) → TC String
printConAs (s , T) = do
  formatErrorParts $ strErr s ∷ space ∷ strErr ":" ∷ space ∷ termErr T ∷ []

printConsAs : List (String × Type) → TC (List String)
printConsAs = mapM printConAs

-- Currently unusable due to datatype not being in scope when printing constructor types with datatype recursion.
printDataAs : (String × Type × ℕ) → List (String × Type) → TC String
printDataAs (s , T , pars) cs = do
  let tel , a = splitType pars T

  sig  ← printDataSignature tel a
  decl ← formatErrorParts $ mergeSpace $
    strErr "data" ∷ space ∷ strErr s ∷ space ∷ [] <> sig <> space ∷ strErr "where" ∷ []

  cons ← vcat ∘ nest <$> extend*Context tel (printConsAs cs)
  return (vcat $ decl ∷ cons ∷ [])

removeImplicitDot : Args Pattern → Args Pattern
removeImplicitDot = filter λ where
  (arg (arg-info hidden _) (dot _)) → false
  t → true

printPattern : Pattern → TC ErrorParts
printPattern (con c as@(_ ∷ _)) = return $
  paren visible (toErr $ con c (removeImplicitDot as))
printPattern p                 = return $ toErr p

--TisP : Term → Pattern → Bool
--TisP (var x args) (var y) = x == y
--TisP (con c args) (con d ps) = (c == d) ∧ {!!}
--TisP (lit l) (lit k) = l == k
--TisP _ _ = false
--
--termHasPat : Term → Pattern → Bool
--termHasPat t p = anyTerm {!!} {!!} t
--
--patIsUsed : Pattern → Term → Bool
--patIsUsed p t = anyPat (termHasPat t) p
--
--printNecessaryPattern : Term → Bool → Arg Pattern → TC ErrorPart
--printNecessaryPattern t b p = {!!}

printPatterns : Bool → Args Pattern → TC ErrorParts
printPatterns b []       = ⦇ [] ⦈
printPatterns b (p ∷ []) = printArg b p printPattern
printPatterns b (p ∷ ps) = do
  p  ← printArg b p printPattern
  ps ← printPatterns b ps
  return $ p <> space ∷ ps

printClause : Bool → (f : Name) → Clause → TC String
printClause b f (tel ⊢ ps `= t) = do
  tel ← renameUnderscore tel
  extend*Context tel do
    ps  ← mergeSpace ∘ dropWhile (space ==_) <$> printPatterns b ps
    formatErrorParts $ (nameErr f ∷ space ∷ ps) <> space ∷ strErr "=" ∷ space ∷ termErr t ∷ []
printClause b f (absurd-clause tel ps) = extend*Context tel do
  formatErrorParts =<< (λ ps → nameErr f ∷ space ∷ ps) ∘ mergeSpace <$> printPatterns b ps

printClauses : Bool → Name → Clauses → TC (List String)
printClauses b f = mapM (printClause b f)

printSig : Name → TC ErrorParts
printSig f = do
  a ← getType f
  return $ nameErr f ∷ space ∷ strErr ":" ∷ space ∷ termErr a ∷ []

printFunction : Bool → Name → TC ⊤
printFunction b f = do
  `A , cs ← getFunction f
  css ← printClauses b f cs
  debugPrint infoName verbosity =<< printSig f
  debugPrint infoName verbosity $ [ strErr (vcat css) ]
  return tt

macro
  print : Name → Tactic
  print d hole = do
    `dT ← getType d
    caseM getDefinition d of λ where
      (function _)        → printFunction false d
      (data-type pars cs) → printData d
      (record-type c fs)  → typeError $
        strErr "Printing the definition of a record type is currently not supported." ∷ []
      _                   → printSig d >>= debugPrint infoName verbosity
    return tt
