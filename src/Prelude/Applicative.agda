{-# OPTIONS --safe #-}

module Prelude.Applicative where

open import Prelude.Level
open import Prelude.Function

open import Prelude.Functor

private variable
  A B : Set _
  
record Applicative (F : ∀ {a} → Set a → Set a) : Setω where
  infixl 4 _<*>_ _<*_ _*>_
  field
    pure  : A → F A
    _<*>_ : F (A → B) → F A → F B
    overlap ⦃ super}} : Functor F

  _<*_ : {A B : Set ℓ} → F A → F B → F A
  a <* b = ⦇ const a b ⦈

  _*>_ : {A B : Set ℓ} → F A → F B → F B
  a *> b = ⦇ (const id) a b ⦈
open Applicative ⦃...⦄ public

{-# DISPLAY Applicative.pure  _ = pure  #-}
{-# DISPLAY Applicative._<*>_ _ = _<*>_ #-}
{-# DISPLAY Applicative._<*_  _ = _<*_  #-}
{-# DISPLAY Applicative._*>_  _ = _*>_  #-}
