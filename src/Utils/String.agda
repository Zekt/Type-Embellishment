{-# OPTIONS --safe #-}

open import Prelude as P
  hiding (concat; intersperse)

module Utils.String where

open import Agda.Builtin.String
  renaming ( primStringUncons to uncons
           ; primStringToList to toList
           )
           
concat : List String → String
concat = foldr _<>_ ""

intersperse : String → List String → String
intersperse sep = concat ∘ P.intersperse sep
           
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

-- enclose string with parens if it contains a space character
parensIfSpace : String → String
parensIfSpace s with elem ' ' (toList s)
... | true  = parens s
... | false = s


