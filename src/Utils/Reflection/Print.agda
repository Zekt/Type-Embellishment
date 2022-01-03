{-# OPTIONS --safe --without-K -v meta:10 #-}
open import Prelude
  hiding ([_,_])

module Utils.Reflection.Print where

open import Utils.Reflection.Core     
open import Utils.Reflection.Term using (splitType)
open import Utils.Reflection.Tactic

paren : Visibility → ErrorParts → ErrorParts
paren v s = case v of λ where
  visible   → [ strErr "(" ] <> s <> [ strErr ")" ]
  hidden    → [ strErr "{" ] <> s <> [ strErr "}" ]
  instance′ → [ strErr "⦃ "] <> s <> [ strErr " ⦄"]

pattern space = strErr " "

printTelescope : Telescope → TC ErrorParts → TC ErrorParts
printTelescope []             m = m
printTelescope ((s , x) ∷ []) m = do
  ss ← extendContext s x m
  ts ← formatErrorPart (termErr $ unArg x)
  return $ paren (getVisibility x) (strErr s ∷ space ∷ strErr ":" ∷ space ∷ [ strErr ts ]) <> ss
printTelescope ((s , x) ∷ tel) m = do
  ss ← extendContext s x (printTelescope tel m)
  ts ← formatErrorPart (termErr $ unArg x)
  return $ paren (getVisibility x) (strErr s ∷ space ∷ strErr ":" ∷ space ∷ strErr ts ∷ []) <> [ space ] <> ss

printDataSignature : (tel : Telescope) → Type → TC ErrorParts
printDataSignature tel a = printTelescope tel do
    a ← formatErrorPart (termErr a)
    return $ space ∷ strErr ":" ∷ space ∷ [ strErr a ]

printCon : (pars : ℕ) → (c : Name) → TC String
printCon pars c = do
  x ← getType c
  let a = snd $ splitType pars x
  formatErrorParts $ nameErr c ∷ space ∷ strErr ":" ∷ space ∷ termErr a ∷ []

printCons : (pars : ℕ) → (cs : Names) → TC (List String)
printCons pars = mapM (printCon pars) 

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

printData : Name → TC ⊤
printData d = do
  pars , cs ← getDataDefinition d
  x ← getType d
  let tel , a = splitType pars x

  sig  ← printDataSignature tel a
  decl ← formatErrorParts $ mergeSpace $
    strErr "data" ∷ space ∷ nameErr d ∷ space ∷ [] <> sig <> space ∷ strErr "where" ∷ []  

  cons ← vcat ∘ nest <$> extend*Context tel (printCons pars cs)
  debugPrint "meta" 5 $ [ strErr (vcat $ decl ∷ cons ∷ []) ]

macro
  printDataT : Name → Tactic
  printDataT d _ = printData d

{-
printClause : Clause → TC ErrorParts 
printClause = {!!}

printClauses : Clauses → TC ErrorParts
printClauses = {!!}

printNameWithType : Name → TC ErrorParts
printNameWithType d = (λ `dT → nameErr d ∷ strErr " : " ∷ termErr `dT ∷ []) <$> getType d

-}

-- printDef : Name → TC ErrorParts
-- printDef d = do
--   `dT ← getType d
--   caseM getDefinition d of λ where
--     (function cs)       → {!!}
--     (data-type pars cs) → do
--       {!!}
--     (record-type c fs)  → {!!}
--     (data-cons _)       → printNameWithType d
--     axiom               → do
--       eps ← printNameWithType d
--       return $ strErr "postualte\n  " ∷ eps
--     prim-fun            → {!!}
