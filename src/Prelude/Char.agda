{-# OPTIONS --without-K --safe #-}
module Prelude.Char where

open import Agda.Builtin.Char as C public
  using (Char)

toUpper toLower : Char → Char
toUpper = C.primToUpper
toLower = C.primToLower
