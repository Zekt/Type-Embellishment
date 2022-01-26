{-# OPTIONS --without-K --safe #-}
open import Prelude

module Generics.Reflection.Recursion where

open import Utils.Reflection
open import Utils.Error as Err

open import Generics.Telescope
open import Generics.Algebra
open import Generics.Description 
open import Generics.Recursion   

open import Generics.Reflection.Telescope
open import Generics.Reflection.Name

normaliseClause : Clause → TC Clause
normaliseClause (tel ⊢ ps `= t) = do
  u ← extend*Context tel $ normalise t
  return $ tel ⊢ ps `= u
normaliseClause cl = return cl

normaliseClauses : Clauses → TC Clauses
normaliseClauses = mapM normaliseClause

checkClauses : Clauses → Type → TC Clauses
checkClauses cls `A = do
  pat-lam₀ cls ← checkType (pat-lam₀ cls) `A
    where _ → IMPOSSIBLE
  return cls

private
  prependLevels : ℕ → Type → Type
  prependLevels n = prependToType (`Levels n)

  pattern `fold-base = quote fold-base
  pattern `ind-base  = quote ind-base

  -- Generate the corresponding clause of a given constructor name
  conClause : (rec : Name) → (pars #levels : ℕ) → Telescope → Name → TC Clause
  conClause rec pars #levels Γps c = do
    Γc ← forgetTypes <$> getConTelescope c pars

    let Γℓs = `Levels #levels
    let |Γc|  = length Γc ; |Γps| = length Γps
    let (_ , cArgs , cPats)   = cxtToVars 0              (`tt , `tt) Γc 
    let (_ , psArgs , psPats) = cxtToVars |Γc|           (`tt , `tt) Γps
    let (_ , ℓArgs , ℓPats)          = cxtToVars (|Γc| + |Γps|) (`tt , `tt) Γℓs

    let cl = show $ (Γℓs <> Γps <> Γc)
               ⊢ ℓPats <> psPats <> vArg (con c cPats) ∷ [] `=
                 (def rec $ ℓArgs <> psArgs <> [ vArg (con c $ hUnknowns pars <> cArgs) ])

    return $ (Γℓs <> Γps <> Γc)
      ⊢ ℓPats <> psPats <> vArg (con c cPats) ∷ [] `=
        (def rec $ ℓArgs <> psArgs <> [ vArg (con c $ hUnknowns pars <> cArgs) ])

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

  renameTypeTo : Type → List String → Type
  renameTypeTo (`Π[ _ ∶ a ] x) (s ∷ ss) = `Π[ s ∶ a ] (renameTypeTo x ss)
  renameTypeTo t _ = t

  renameTelTo : Telescope → List String → Telescope
  renameTelTo ((_ , x) ∷ tel) (s ∷ ss) = (s , x) ∷ renameTelTo tel ss
  renameTelTo tel _ = tel

defineFold : FoldP → Name → TC _
defineFold P f = do
  `P ← quoteωTC P
  `type ← prependLevels #levels <$> extendContextℓs #levels λ ℓs → do
      ss ← fromTelInfo (ParamN {ℓs})
      T  ← quoteTC! (FoldNT P ℓs)
      return $ renameTypeTo T ss

  declareDef (vArg f) (unConflictType `type)

  let rec = def₂ `fold-base `P (def₀ f)
  dummyRec ← freshName ""
  declareDef (vArg dummyRec) `type
  defineFun dummyRec [ [] ⊢ [] `= rec ]
  pars , cs ← getDataDefinition =<< FoldPToNativeName P

  cls ← extendContextℓs #levels λ ℓs → do
    Γps ← fromTel! (Param ℓs) ParamV
    ss  ← fromTelInfo (ParamN {ℓs})
    forM cs $ conClause dummyRec pars #levels (renameTelTo Γps ss)
  cls ← noConstraints $ normaliseClauses =<< checkClauses cls `type

  defineFun f cls
  printFunction false f
  where open FoldP P

defineInd : IndP → Name → TC _
defineInd P f = do
  `P    ← quoteωTC P
  `type ← prependLevels #levels <$> extendContextℓs #levels λ ℓs → do
    ss ← fromTelInfo (ParamN {ℓs})
    T  ← quoteTC! (IndNT P ℓs)
    return $ renameTypeTo T ss
  declareDef (vArg f) `type

  let ind = def₂ `ind-base `P (def₀ f)
  dummyRec ← freshName ""
  declareDef (vArg dummyRec) (unConflictType `type)
  defineFun dummyRec [ [] ⊢ [] `= ind ]

  pars , cs ← getDataDefinition =<< IndPToNativeName P

  cls ← extendContextℓs #levels λ ℓs → do
    Γps ← fromTel! (Param ℓs) ParamV
    ss  ← fromTelInfo (ParamN {ℓs})
    forM cs $ conClause dummyRec pars #levels (renameTelTo Γps ss)

  cls ← noConstraints $ normaliseClauses =<< checkClauses cls `type

  defineFun f cls

  printFunction false f
  where open IndP P
