{-# OPTIONS --safe --without-K #-}
open import Prelude
  hiding ([_,_])

module Utils.Reflection.Print where

open import Utils.Reflection.Core     
open import Utils.Reflection.Term
  using (splitType)
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

vcat : List String → String
vcat []           = ""
vcat (msg ∷ [])   = msg 
vcat (msg ∷ msgs) = msg <> "\n" <> vcat msgs 

sep : ErrorParts → ErrorParts
sep []       = []
sep (e ∷ []) = e ∷ []
sep (e ∷ es) = e ∷ space ∷ sep es

nest : List String → List String
nest = map ("  " <>_) 

mergeSpace : ErrorParts → ErrorParts
mergeSpace []                     = []
mergeSpace (space ∷ space ∷ msg)  = mergeSpace (space ∷ msg)
mergeSpace (err   ∷ errs)         = err ∷ mergeSpace errs

printArg : Arg A → (A → TC ErrorParts) → TC ErrorParts
printArg x f = case getVisibility x of λ where
  visible → do
    err ← f (unArg x)
    return $ if elem space err
      then paren visible err
      else err
  v → paren v <$> f (unArg x)
  
printTelescope : Telescope → TC ErrorParts → TC ErrorParts
printTelescope []             m = m
printTelescope ((s , x) ∷ []) m = do
  ss ← extendContext s x m
  s  ← extendContext s x (formatErrorPart $ termErr (var₀ 0))
  ts ← formatErrorPart (termErr $ unArg x)
  return $ paren (getVisibility x) (strErr s ∷ colon ∷ [ strErr ts ]) <> ss
printTelescope ((s , x) ∷ tel) m = do
  ss ← extendContext s x $ printTelescope tel m
  s  ← extendContext s x (formatErrorPart $ termErr (var₀ 0))
  ts ← formatErrorPart (termErr $ unArg x)
  return $ paren (getVisibility x) (strErr s ∷ space ∷ strErr ":" ∷ space ∷ [ strErr ts ]) <> space ∷ ss

printDataSignature : (tel : Telescope) → Type → TC ErrorParts
printDataSignature tel a = printTelescope tel do
    a ← formatErrorPart $ termErr a
    return $ space ∷ strErr ":" ∷ space ∷ [ strErr a ]

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

printPattern : Pattern → TC ErrorParts
printPattern p@(con c (_ ∷ _)) = return $ paren visible [ pattErr p ]
printPattern p                 = return $ [ pattErr p ]

printPatterns : Args Pattern → TC ErrorParts
printPatterns []       = ⦇ [] ⦈
printPatterns (p ∷ []) = printArg p printPattern
printPatterns (p ∷ ps) = do
  p  ← printArg p printPattern
  ps ← printPatterns ps
  return $ p <> space ∷ ps

printClause : (f : Name) → Clause → TC String 
printClause f (tel ⊢ ps `= t) = do
  tel ← renameUnderscore tel
  extend*Context tel do
    ps  ← printPatterns ps
    formatErrorParts $ (nameErr f ∷ space ∷ ps) <> space ∷ strErr "=" ∷ space ∷ termErr t ∷ []
printClause f (absurd-clause tel ps) = extend*Context tel do
  formatErrorParts =<< (λ ps → nameErr f ∷ space ∷ ps) <$> printPatterns ps      

printClauses : Name → Clauses → TC (List String)
printClauses f = mapM (printClause f)

printSig : Name → TC ErrorParts
printSig f = do
  a ← getType f
  return $ nameErr f ∷ space ∷ strErr ":" ∷ space ∷ termErr a ∷ []

printFunction : Name → TC ⊤
printFunction f = do
  `A , cs ← getFunction f
  css ← printClauses f cs
  debugPrint infoName verbosity =<< printSig f
  debugPrint infoName verbosity $ [ strErr (vcat css) ]
  return tt


macro
  print : Name → Tactic
  print d hole = do
    `dT ← getType d
    caseM getDefinition d of λ where
      (function _)        → printFunction d
      (data-type pars cs) → printData d
      (record-type c fs)  → typeError $
        strErr "Printing the definition of a record type is currently not supported." ∷ []
      _                   → printSig d >>= debugPrint infoName verbosity
    return tt

