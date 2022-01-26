{-# OPTIONS --without-K --safe #-}
module Prelude.Char where

open import Agda.Builtin.Char as C public
  using (Char)

open import Agda.Builtin.Nat
open import Prelude.Maybe
open import Prelude.Bool
open import Prelude.Nat
open import Prelude.List

toUpper toLower : Char → Char
toUpper = C.primToUpper
toLower = C.primToLower

toNat : Char → Maybe Nat
toNat c = let n = C.primCharToNat c
           in if (47 <ᵇ n) ∧ (n <ᵇ 58) then
                just (n ∸ 48)
              else
                nothing

fromNat : Nat → Maybe Char
fromNat n = if (0 ≤? n) ∧ (n <ᵇ 10) then
              just (C.primNatToChar (n + 48))
            else
              nothing

lenLeadingNat : List Char → Nat
lenLeadingNat [] = 0
lenLeadingNat (x ∷ xs) = if C.primIsDigit x then
                           suc (lenLeadingNat xs)
                         else 0
