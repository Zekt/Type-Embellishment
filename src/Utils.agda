module Utils where

open import Prelude


-- lookup from last
lookupCxt : ∀ {A : Set} → List A → ℕ → Maybe A
lookupCxt = lookup

-- Only one kind of difference is acceptable.
S&Rs : Term → (Term → Term) → List (Arg Term) → List (Arg Term) → List (Maybe Term)
S&R : Term → (Term → Term) → Term → Term → Maybe Term

{-# TERMINATING #-}
S&Rs inner f [] [] = []
S&Rs inner f (arg _ x ∷ xs) (arg _ y ∷ ys) = S&R inner f x y ∷ S&Rs inner f xs ys
S&Rs inner f _ _ = []

S&R inner f x y =
  if (does $ y ≟ inner)
    then just (f x)
  else case (x , y) of λ where
         (var m args₁ , var n args₂) →
           if suc m == n
             then maybes (S&Rs inner f args₁ args₂)
             else nothing
         (con c args₁ , con d args₂) →
           if (does (c ≟ d))
             then (maybes $ S&Rs inner f args₁ args₂)
             else nothing
         (def c args₁ , def d args₂) →
           if (does (c ≟ d))
             then (maybes $ S&Rs inner f args₁ args₂)
             else nothing
         (_ , _) → nothing

{-# TERMINATING #-}
S&Rrec : Term → (Term → Term) → Term → Term → Maybe Term
S&Rrec inner f term pat = S&R inner f term pat
                      <∣> (case term of λ where
                            (var x args) → just (var x $ S&Rargs args)
                            (con c args) → just (con c $ S&Rargs args)
                            (def f args) → just (def f $ S&Rargs args)
                            (lam v t) → just (lam v (map fromMaybeId t))
                            t → just t)
  where
    fromMaybeId : Term → Term
    fromMaybeId t = fromMaybe t (S&Rrec inner f t pat)

    S&Rargs : List (Arg Term) → List (Arg Term)
    S&Rargs args = map fromMaybeId args
