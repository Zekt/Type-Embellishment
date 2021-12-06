{-# OPTIONS --safe #-}

module Prelude.Functor where

open import Agda.Primitive

private variable
  A B : Set _

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
