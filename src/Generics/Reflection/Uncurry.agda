{-# OPTIONS --safe --without-K --show-implicit #-}
open import Prelude

module Generics.Reflection.Uncurry where

open import Utils.Reflection
open import Utils.Error as Err

open import Generics.Telescope
open import Generics.Reflection.Constructor
open import Generics.Reflection.Telescope

------------------------------------------------------------------------
-- Meta-level currying operations

private
-- Check if the given telescope is a prefix of a telescope up to arg-info 
-- and return the telescope with the correct visibility
  _isPrefixOf_ : Telescope → Telescope → TC Telescope
  _isPrefixOf_ []                   Δ                    = return []
  _isPrefixOf_ ((_ , A) ∷ Γ)        []                   = typeError $
    strErr "An extra argument of type" ∷ termErr (unArg A) ∷ strErr " to apply" ∷ []
  _isPrefixOf_ ((_ , arg _ `A) ∷ Γ) ((s , arg i `B) ∷ Δ) = do
    unify `A `B <|> (typeError $ termErr `A ∷ strErr " ≠ " ∷ termErr `B ∷ [])
    extendContext s (vArg `B) do
      (s , arg i `B) ∷_ <$> (Γ isPrefixOf Δ)

cmpTelWithType : Telescope → Type → TC Telescope
cmpTelWithType Γ `A =
  let Δ , `B = ⇑ `A ⦂ Telescope × Type in Γ isPrefixOf Δ

------------------------------------------------------------------------
-- Uncurrying by `Tel`

UncurriedᵗTC : (T : Tel ℓ) → TC Type
UncurriedᵗTC T = vΠ[ "t" ∶_] unknown <$> quoteTC ⟦ T ⟧ᵗ

uncurryᵗTC : (T : Tel ℓ) → Term → TC Term
uncurryᵗTC T t = do
  Γ   ← fromTel T 
  `A  ← inferNormalisedType t
  Γ   ← cmpTelWithType Γ `A
  let ((_ , p) , (args , _)) = cxtToVars (`tt , `tt) Γ 
  return $ pat-lam [ Γ ⊢ [ vArg p ] `= (t `$$ args) ] []

macro
  `uncurryᵗ : Tel ℓ → Term → Tactic
  `uncurryᵗ T t hole = do
    hole ← checkType hole =<< UncurriedᵗTC T
    unify hole =<< uncurryᵗTC T t

------------------------------------------------------------------------
-- Uncurrying by # of levels

UncurriedℓsTC : (#levels : ℕ) → TC Type
UncurriedℓsTC n = vΠ[ "ℓs" ∶_] unknown <$> quoteTC! (Level ^ n)

uncurryℓsTC : (#levels : ℕ) → Term → TC Term
uncurryℓsTC n t = do
  `A ← inferNormalisedType t
  Γ  ← cmpTelWithType (duplicate n $ "ℓ" , vArg `Level) `A 
  let (_ , p) , (args , _) = cxtToVars (`tt , `tt) Γ
  return $ pat-lam [ Γ ⊢ [ vArg p ] `= (t `$$ args) ] []

macro
  `uncurryℓs : (#levels : ℕ) → Term → Tactic
  `uncurryℓs n t hole = do
--    hole ← checkType hole =<< UncurriedℓsTC n
    unify hole =<< uncurryℓsTC n t

-- data Vec (A : Set) : ℕ → Set where

-- VecT = genTel (fst $ getTelescopeT Vec)

-- Vec-wrapper : ⟦ VecT ⟧ᵗ → Set
-- Vec-wrapper = λ (A , n , tt) → Vec A n

-- tel : Tel _ 
-- tel = [ A ∶ Set ] []

private
  L′ : (ℓs : Level ^ 1) → (A : Set (fst ℓs)) → Set (fst ℓs)
  L′ = `uncurryℓs 1 (List)
