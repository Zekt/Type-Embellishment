{-# OPTIONS --safe --with-K #-}

module Examples.WithMacros.BST where

open import Prelude hiding (lookupAny)

open import Utils.Reflection.Print

open import Generics.Description
open import Generics.Recursion
open import Generics.Reflection

open import Generics.Ornament
open import Generics.Ornament.Description
open import Generics.Ornament.Algebraic
open import Generics.Ornament.Algebraic.Isomorphism
open import Generics.SimpleContainer
open import Generics.SimpleContainer.All
open import Generics.SimpleContainer.Any

Height : Set
Height = ℕ

Value : Set
Value = ℕ

variable
  h l r : ℕ

data B23Tree : Height → Value → Value → Set where

  node₀ : ⦃ l ≤ r ⦄
        → -------------
          B23Tree 0 l r

  node₂ : (x : Value)
        → B23Tree h l x → B23Tree h x r
        → -----------------------------
          B23Tree (suc h) l r

  node₃ : (x y : Value)
        → B23Tree h l x → B23Tree h x y → B23Tree h y r
        → ---------------------------------------------
          B23Tree (suc h) l r

B23TreeD = genDataD B23Tree
B23TreeC = genDataC B23TreeD (genDataT B23TreeD B23Tree)

B23TreeS : SCᵈ B23TreeD
B23TreeS = record
  { El  = λ _ → ℕ
  ; pos = (false ∷ false ∷ false ∷ [])
        ∷ (false ∷ false ∷ false ∷ true ∷ tt ∷ tt ∷ [])
        ∷ (false ∷ false ∷ false ∷ true ∷ true ∷ tt ∷ tt ∷ tt ∷ []) ∷ []
  ; coe = λ _ → (λ _ _ _ → lift tt)
            ,ωω (λ _ _ _ → refl ,ωω λ _ → lift tt)
            ,ωω (λ _ _ _ → refl ,ωω λ _ → refl ,ωω λ _ → lift tt) ,ωω lift tt }

--------
-- All predicate

B23TreePOD : DataOD B23TreeD
B23TreePOD = PredOD B23TreeC B23TreeS
B23TreePD = ⌊ B23TreePOD ⌋ᵈ

unquoteDecl data B23TreeP constructor c0 c1 c2 = defineByDataD B23TreePD B23TreeP (c0 ∷ c1 ∷ c2 ∷ [])
-- data B23TreeP (P : Value → Set ℓ) : Height → Value → Value → Set ℓ where
--
--   node₀ : ⦃ l ≤ r ⦄
--         → ----------------
--           B23TreeP P 0 l r
--
--   node₂ : (x : Value) → P x
--         → B23TreeP P h l x → B23TreeP P h x r
--         → -----------------------------------
--           B23TreeP P (suc h) l r
--
--   node₃ : (x : Value) → P x → (y : Value) → P y
--         → B23TreeP P h l x → B23TreeP P h x y → B23TreeP P h y r
--         → ------------------------------------------------------
--           B23TreeP P (suc h) l r

B23TreePC = genDataC B23TreePD (genDataT B23TreePD B23TreeP)

B23TreePFin : Finitary B23TreePD
B23TreePFin = (tt ∷ tt ∷ tt ∷ [])
              ∷ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ refl ∷ refl ∷ [])
              ∷ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ refl ∷ refl ∷ refl ∷ []) ∷ []

toB23TreeP : FoldP
toB23TreeP = forget B23TreePC B23TreeC ⌈ B23TreePOD ⌉ᵈ

unquoteDecl toB23Tree = defineFold toB23TreeP toB23Tree
-- toB23Tree : ∀ {P : ℕ → Set ℓ} {h l r} → B23TreeP P h l r → B23Tree h l r
-- toB23Tree  node₀                 = node₀
-- toB23Tree (node₂ x p      t u  ) = node₂ x   (toB23Tree t) (toB23Tree u)
-- toB23Tree (node₃ x p y p' t u v) = node₃ x y (toB23Tree t) (toB23Tree u) (toB23Tree v)

toB23TreeC = genFoldC toB23TreeP toB23Tree

B23TreeAllOD : DataOD B23TreePD
B23TreeAllOD = AllOD B23TreeC B23TreeS B23TreePC
B23TreeAllD = ⌊ B23TreeAllOD ⌋ᵈ

unquoteDecl data B23TreeAll constructor c0′ c1′ c2′ = defineByDataD B23TreeAllD B23TreeAll (c0′ ∷ c1′ ∷ c2′ ∷ [])
-- data B23TreeAll (P : Value → Set ℓ) : ∀ {h l r} → B23Tree h l r → Set ℓ where
-- 
--   node₀ : ⦃ _ : l ≤ r ⦄
--         → ------------------------------
--           B23TreeAll P {0} {l} {r} node₀
-- 
--   node₂ : ∀ {x} → P x
--         → ∀ {t} → B23TreeAll P {h} {l} {x} t
--         → ∀ {u} → B23TreeAll P {h} {x} {r} u
--         → ----------------------------------
--           B23TreeAll P (node₂ x t u)
-- 
--   node₃ : ∀ {x} → P x → ∀ {y} → P y
--         → ∀ {t} → B23TreeAll P {h} {l} {x} t
--         → ∀ {u} → B23TreeAll P {h} {x} {y} u
--         → ∀ {v} → B23TreeAll P {h} {y} {r} v
--         → ----------------------------------
--           B23TreeAll P (node₃ x y t u v)

B23TreeAllT = genDataT B23TreeAllD B23TreeAll
B23TreeAllC = genDataC B23TreeAllD B23TreeAllT 

fromAllP : FoldP
fromAllP = forget B23TreeAllC B23TreePC ⌈ B23TreeAllOD ⌉ᵈ

unquoteDecl fromAll = defineFold fromAllP fromAll

fromAllC = genFoldC fromAllP fromAll

toAllP : IndP
toAllP = remember toB23TreeC B23TreeAllC

unquoteDecl toAll = defineInd toAllP toAll

toAllC = genIndC toAllP toAll

--from-toAllP : IndP
--from-toAllP = forget-remember-inv toB23TreeC B23TreeAllC fromAllC toAllC (inl B23TreePFin)

--unquoteDecl from-toAll = defineInd from-toAllP from-toAll

--from-toAllC = genIndC from-toAllP from-toAll

--to-fromAllP : IndP
--to-fromAllP = remember-forget-inv toB23TreeC B23TreeAllC fromAllC toAllC (inl B23TreePFin)

--unquoteDecl to-fromAll = defineInd to-fromAllP to-fromAll


--to-fromAllC = genIndC to-fromAllP to-fromAll

--------
-- Any predicate

B23TreeAnyD : DataD
B23TreeAnyD = ⌊ AnyOD B23TreeC B23TreeS ⌋ᵈ

unquoteDecl data B23TreeAny constructor b23any0 b23any1 b23any2 b23any3 b23any4 b23any5 b23any6 b23any7 = defineByDataD B23TreeAnyD B23TreeAny (b23any0 ∷ b23any1 ∷ b23any2 ∷ b23any3 ∷ b23any4 ∷ b23any5 ∷ b23any6 ∷ b23any7 ∷ [])
--data B23TreeAny (P : Value → Set ℓ) : ∀ {h l r} → B23Tree h l r → Set ℓ where
--  node₂-here   : ∀ {x   t u  } → P x → B23TreeAny P {suc h} {l} {r} (node₂ x   t u  )
--  node₃-here₀  : ∀ {x y t u v} → P x → B23TreeAny P {suc h} {l} {r} (node₃ x y t u v)
--  node₃-here₁  : ∀ {x y t u v} → P y → B23TreeAny P {suc h} {l} {r} (node₃ x y t u v)
--  node₂-there₀ : ∀ {x   t u  } → B23TreeAny P t
--               → B23TreeAny P {suc h} {l} {r} (node₂ x   t u  )
--  node₂-there₁ : ∀ {x   t u  } → B23TreeAny P u
--               → B23TreeAny P {suc h} {l} {r} (node₂ x   t u  )
--  node₃-there₀ : ∀ {x y t u v} → B23TreeAny P t
--               → B23TreeAny P {suc h} {l} {r} (node₃ x y t u v)
--  node₃-there₁ : ∀ {x y t u v} → B23TreeAny P u
--               → B23TreeAny P {suc h} {l} {r} (node₃ x y t u v)
--  node₃-there₂ : ∀ {x y t u v} → B23TreeAny P v
--               → B23TreeAny P {suc h} {l} {r} (node₃ x y t u v)

B23TreeAnyT = genDataT B23TreeAnyD B23TreeAny
B23TreeAnyC = genDataC B23TreeAnyD B23TreeAnyT

lookupB23TreeAnyP : FoldP
lookupB23TreeAnyP = lookupAny B23TreeC B23TreeS B23TreeAnyC

unquoteDecl lookupB23TreeAny = defineFold lookupB23TreeAnyP lookupB23TreeAny

lookupB23TreeAnyC = genFoldC lookupB23TreeAnyP lookupB23TreeAny
