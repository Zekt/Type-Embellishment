{-# OPTIONS --safe #-}
module Prelude.Maybe where

open import Agda.Builtin.Unit
  using (⊤; tt)
open import Agda.Builtin.List
  using (List; []; _∷_)
open import Agda.Builtin.Bool

open import Prelude.Function
open import Prelude.Functor

private variable
  A B C : Set _

open import Agda.Builtin.Maybe public
  using (Maybe; just; nothing)

instance
  MaybeFuntor : Functor Maybe
  fmap ⦃ MaybeFuntor ⦄ f (just x) = just (f x)
  fmap ⦃ MaybeFuntor ⦄ f nothing  = nothing
  
-- A dependent eliminator.

maybe : ∀ {a b} {A : Set a} {B : Maybe A → Set b} →
        ((x : A) → B (just x)) → B nothing → (x : Maybe A) → B x
maybe j n (just x) = j x
maybe j n nothing  = n


-- A non-dependent eliminator.
maybe′ : (A → B) → B → Maybe A → B
maybe′ = maybe

-- A defaulting mechanism

fromMaybe : A → Maybe A → A
fromMaybe = maybe′ id

boolToMaybe : Bool → Maybe ⊤
boolToMaybe true  = just tt
boolToMaybe false = nothing

when : Bool → A → Maybe A
when b c = (λ _ → c) <$> (boolToMaybe b)

-- Alternative: <∣>

_<∣>_ : Maybe A → Maybe A → Maybe A
just x  <∣> my = just x
nothing <∣> my = my

maybes : {A : Set} → List (Maybe A) → Maybe A
maybes []       = nothing
maybes (x ∷ xs) = x <∣> maybes xs
