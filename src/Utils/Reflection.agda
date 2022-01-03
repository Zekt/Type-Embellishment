{-# OPTIONS --safe --without-K -v meta:10 #-}
open import Prelude
  hiding ([_,_])

module Utils.Reflection where

open import Utils.Reflection.Core     public
open import Utils.Reflection.Eq       public
open import Utils.Reflection.Show     public
open import Utils.Reflection.Term     public
open import Utils.Reflection.Tactic   public
open import Utils.Reflection.Print    public

