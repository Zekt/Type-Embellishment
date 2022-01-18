{-# OPTIONS --safe --without-K #-}

open import Prelude

module Generics.Reflection.Constructor where

open import Utils.Reflection
open import Utils.Error          as Err

open import Generics.Telescope
open import Generics.Description 

private
  variable
    T U : Tel ℓ

pattern `[]      = con₀ (quote ConDs.[])
pattern _`∷_ x y = con₂ (quote ConDs._∷_) x y
pattern `ιʳ  x   = con₁ (quote RecD.ι)    x
pattern `π   x y = con₂ (quote RecD.π)    x y
pattern `ιᶜ  x   = con₁ (quote ConD.ι)    x
pattern `σ   x y = con₂ (quote ConD.σ)    x y
pattern `ρ   x y = con₂ (quote ConD.ρ)    x y

------------------------------------------------------------------------
-- Each constructor `c : (x₁ : A₁) → (x₂ : A₂ x₁) → ⋯ → T`
-- can be represented as a pattern on the LHS `c x₁ x₂ ⋯ xₙ` or as a term on the RHS
-- They can be also uncurried described by ⟦ ConD ⟧. Thus, there are 4 types of constructor representations. 
cxtToVars : (base : Term × Pattern) → (Γ : Telescope) → (Term × Pattern) × (Args Term × Args Pattern)
cxtToVars base = snd ∘ foldr emptyVar λ where
      (_ , arg i _) (n , (t , p) , (targs , pargs)) →
        suc n , ((var₀ n `, t) , (var n `, p)) , (arg i (var₀ n) ∷ targs) , (arg i (var n) ∷ pargs)
  where emptyVar = 0 , base , ([] , [])

cxtToVarPatt : Telescope → Pattern
cxtToVarPatt Γ = let (_ , p) , _ = cxtToVars (`tt , `tt) Γ in p

-- Translate the semantics of an object-level telescope to a context
idxToArgs : ⟦ T ⟧ᵗ → TC (Args Term)
idxToArgs {T = []}     tt      = ⦇ [] ⦈
idxToArgs {T = _ ∷ _}  (A , Γ) = ⦇ ⦇ vArg (quoteTC A) ⦈ ∷ (idxToArgs Γ) ⦈
idxToArgs {T = _ ++ _} (T , U) = ⦇ (idxToArgs T) <> (idxToArgs U) ⦈

-- The fully applied datatype 
typeOfData : Name → (ps : ⟦ U ⟧ᵗ) (is : ⟦ T ⟧ᵗ) → TC Type 
typeOfData d ps is = ⦇ (def d) ⦇ (idxToArgs ps) <> (idxToArgs is) ⦈ ⦈ 
-- ... and back
argsToIdx : Args Term → Term
argsToIdx []       = `tt
argsToIdx (x ∷ xs) = (unArg x) `, argsToIdx xs

to`ConDs : Terms → Term
to`ConDs = foldr `[] _`∷_
