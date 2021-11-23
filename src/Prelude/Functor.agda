module Prelude.Functor where

open import Agda.Primitive
open import Agda.Builtin.Reflection

open import Prelude.List as L
  using (List; []; _∷_)
open import Prelude.Maybe as M
  using (Maybe)

private variable
  A B : Set _

record Functor (F : ∀ {a} → Set a → Set a) : Setω where 
  infixl 4 _<$>_ _<$_

  field
    map : (A → B) → F A → F B

  _<$>_ : (A → B) → F A → F B
  _<$>_ = map
  {-# INLINE _<$>_ #-}

  _<$_ : A → F B → F A
  x <$ m = map (λ _ → x) m
  {-# INLINE _<$_ #-}
open Functor {{...}} public 

{-# DISPLAY Functor.map   _ = map  #-}
{-# DISPLAY Functor._<$>_ _ = _<$>_ #-}
{-# DISPLAY Functor._<$_  _ = _<$_  #-}

instance
  ListFunctor : Functor List
  map ⦃ ListFunctor ⦄ = L.map

  MaybeFuntor : Functor Maybe
  map ⦃ MaybeFuntor ⦄ = M.map

  TCFunctor : Functor TC
  map ⦃ TCFunctor ⦄ f xs = bindTC xs λ x → returnTC (f x)

  ArgFunctor : Functor Arg
  map ⦃ ArgFunctor ⦄ f (arg i x) = arg i (f x)

  ArgsFunctor : Functor λ A → List (Arg A)
  map ⦃ ArgsFunctor ⦄ f []       = []
  map ⦃ ArgsFunctor ⦄ f (x ∷ xs) = map f x ∷ map f xs

  AbsFunctor : Functor Abs
  map ⦃ AbsFunctor ⦄ f (abs s x) = abs s (f x)
