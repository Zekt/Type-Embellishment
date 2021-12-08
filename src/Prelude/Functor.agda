{-# OPTIONS --safe #-}

module Prelude.Functor where

open import Agda.Primitive

open import Prelude.Function
open import Prelude.Relation.PropositionalEquality

private variable
  A B C : Set _

record Functor (F : ∀ {a} → Set a → Set a) : Setω where 
  infixl 4 _<$>_ _<$_

  field
    fmap : (A → B) → F A → F B

  _<$>_ : (A → B) → F A → F B
  _<$>_ = fmap
  {-# INLINE _<$>_ #-}

  _<$_ : A → F B → F A
  x <$ m = fmap (λ _ → x) m
  {-# INLINE _<$_ #-}
open Functor {{...}} public 

{-# DISPLAY Functor.fmap  _ = fmap  #-}
{-# DISPLAY Functor._<$>_ _ = _<$>_ #-}
{-# DISPLAY Functor._<$_  _ = _<$_  #-}

record FunctorLaw (F : ∀ {a} → Set a → Set a) : Setω where
  field
    overlap ⦃ super ⦄ : Functor F

    fmap-cong : ∀ {a b} {A : Set a} {B : Set b} → (f g : A → B) → ((x : A) → f x ≡ g x)
      → (x : F A) → fmap f x ≡ fmap g x
    fmap-id   : ∀ {a} {A : Set a} (x : F A) → fmap id x ≡ x
    fmap-comp : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
      → (f : B → C) (g : A → B)
      → (x : F A)
      → fmap (f ∘ g) x ≡ (fmap f ∘ fmap g) x

open FunctorLaw ⦃ ... ⦄ public

{-# DISPLAY FunctorLaw.fmap-cong _ = fmap-cong  #-}
--{-# DISPLAY FunctorLaw.fmap-id   _ = fmap-id    #-}
--{-# DISPLAY FunctorLaw.fmap-comp _ = fmap-comp  #-}
