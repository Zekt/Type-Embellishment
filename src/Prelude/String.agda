{-# OPTIONS --without-K --safe #-}
module Prelude.String where

open import Agda.Builtin.Char
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat hiding (_==_)
open import Agda.Builtin.List

open import Prelude.Eq
open import Prelude.List
open import Prelude.Char
open import Prelude.Coercion
open import Prelude.Monoid
open import Prelude.Maybe
open import Prelude.Function

open import Agda.Builtin.String as S public
  using (String)

parens : String → String
parens s = "(" <> s <> ")"

braces : String → String
braces s = "{" <> s <> "}"

-- append that also introduces spaces, if necessary
infixr 5 _<+>_
_<+>_ : String → String → String
"" <+> b = b
a <+> "" = a
a <+> b = a <> " " <> b

instance
  StringToList : Coercion' String (List Char)
  ⇑_ ⦃ StringToList ⦄ = S.primStringToList 

  ListToString : Coercion' (List Char) String
  ⇑_ ⦃ ListToString ⦄ = S.primStringFromList

-- enclose string with parens if it contains a space character
parensIfSpace : String → String
parensIfSpace s with hasSpace (⇑ s)
  where
    hasSpace : List Char → Bool
    hasSpace []       = false
    hasSpace (x ∷ xs) with x == ' '
    ... | true  = true 
    ... | false = hasSpace xs
... | true  = parens s
... | false = s

trailingNatʳ : List Char → Maybe Nat
trailingNatʳ [] = nothing
trailingNatʳ (x ∷ xs) with toNat x
... | (just x) = case trailingNatʳ xs of λ where
                   (just x') → just (x' * 10 + x)
                   nothing → just x
... | nothing = nothing

trailingNat = trailingNatʳ ∘ reverse
lenTrailingNat = lenLeadingNat ∘ reverse

increase : String → String
increase s with ⇑ s
... | cs = case trailingNat cs of λ where
             (just x) → (⇑ removeLast (lenTrailingNat cs) cs) <>
                        S.primShowNat (suc x)
             nothing  → s <> "1"

