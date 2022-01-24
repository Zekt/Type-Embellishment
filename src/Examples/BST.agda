{-# OPTIONS --safe --with-K #-}

module Examples.BST where

open import Prelude hiding (lookupAny)

open import Utils.Reflection

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
B23TreeS ℓs = record
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
B23TreePOD = PredOD B23TreeD B23TreeS

-- unquoteDecl data B23TreeP constructor c0 c1 c2 = defineByDataD ⌊ B23TreePOD ⌋ᵈ B23TreeP (c0 ∷ c1 ∷ c2 ∷ [])
data B23TreeP (P : Value → Set ℓ) : Height → Value → Value → Set ℓ where

  node₀ : ⦃ l ≤ r ⦄
        → ----------------
          B23TreeP P 0 l r

  node₂ : (x : Value) → P x
        → B23TreeP P h l x → B23TreeP P h x r
        → -----------------------------------
          B23TreeP P (suc h) l r

  node₃ : (x : Value) → P x → (y : Value) → P y
        → B23TreeP P h l x → B23TreeP P h x y → B23TreeP P h y r
        → ------------------------------------------------------
          B23TreeP P (suc h) l r

B23TreePC = genDataC ⌊ B23TreePOD ⌋ᵈ (genDataT ⌊ B23TreePOD ⌋ᵈ B23TreeP)

B23TreePFin : Finitary ⌊ B23TreePOD ⌋ᵈ
B23TreePFin _ = (tt ∷ tt ∷ tt ∷ [])
              ∷ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ refl ∷ refl ∷ [])
              ∷ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ refl ∷ refl ∷ refl ∷ []) ∷ []

toB23TreeP : FoldP
toB23TreeP = forget B23TreePC B23TreeC ⌈ B23TreePOD ⌉ᵈ

-- unquoteDecl toB23Tree = defineFold toB23TreeP toB23Tree
toB23Tree : ∀ {P : ℕ → Set ℓ} {h l r} → B23TreeP P h l r → B23Tree h l r
toB23Tree  node₀                 = node₀
toB23Tree (node₂ x p      t u  ) = node₂ x   (toB23Tree t) (toB23Tree u)
toB23Tree (node₃ x p y p' t u v) = node₃ x y (toB23Tree t) (toB23Tree u) (toB23Tree v)

toB23TreeC = genFoldC toB23TreeP toB23Tree

B23TreeAllOD : DataOD ⌊ B23TreePOD ⌋ᵈ
B23TreeAllOD = AllOD B23TreeC B23TreeS B23TreePC

-- unquoteDecl data B23TreeAll constructor c0 c1 c2 = defineByDataD ⌊ B23TreeAllOD ⌋ᵈ B23TreeAll (c0 ∷ c1 ∷ c2 ∷ [])
data B23TreeAll (P : Value → Set ℓ) : ∀ {h l r} → B23Tree h l r → Set ℓ where

  node₀ : ⦃ _ : l ≤ r ⦄
        → ------------------------------
          B23TreeAll P {0} {l} {r} node₀

  node₂ : ∀ {x} → P x
        → ∀ {t} → B23TreeAll P {h} {l} {x} t
        → ∀ {u} → B23TreeAll P {h} {x} {r} u
        → ----------------------------------
          B23TreeAll P (node₂ x t u)

  node₃ : ∀ {x} → P x → ∀ {y} → P y
        → ∀ {t} → B23TreeAll P {h} {l} {x} t
        → ∀ {u} → B23TreeAll P {h} {x} {y} u
        → ∀ {v} → B23TreeAll P {h} {y} {r} v
        → ----------------------------------
          B23TreeAll P (node₃ x y t u v)

B23TreeAllC = genDataC ⌊ B23TreeAllOD ⌋ᵈ (genDataT ⌊ B23TreeAllOD ⌋ᵈ B23TreeAll)

fromAllP : FoldP
fromAllP = forget B23TreeAllC B23TreePC ⌈ B23TreeAllOD ⌉ᵈ

-- unquoteDecl fromAll = defineFold fromAllP fromAll
fromAll : ∀ {P : Value → Set ℓ} {h l r} {t : B23Tree h l r}
        → B23TreeAll P t → B23TreeP P h l r
fromAll  node₀            = node₀
fromAll (node₂ p   t u  ) = node₂ _ p     (fromAll t) (fromAll u)
fromAll (node₃ p q t u v) = node₃ _ p _ q (fromAll t) (fromAll u) (fromAll v)

fromAllC = genFoldC fromAllP fromAll

toAllP : IndP
toAllP = remember toB23TreeC B23TreeAllC

-- unquoteDecl toAll = defineInd toAllP toAll
toAll : ∀ {P : Value → Set ℓ} {h l r} (t : B23TreeP P h l r) → B23TreeAll P (toB23Tree t)
toAll  node₀                = node₀
toAll (node₂ x p     t u  ) = node₂ p   (toAll t) (toAll u)
toAll (node₃ x p y q t u v) = node₃ p q (toAll t) (toAll u) (toAll v)

toAllC = genIndC toAllP toAll

from-toAllP : IndP
from-toAllP = forget-remember-inv toB23TreeC B23TreeAllC fromAllC toAllC (inl B23TreePFin)

-- [FAIL] too slow;  manually case-split and elaborate-and-give
-- unquoteDecl from-toAll = defineInd from-toAllP from-toAll
from-toAll : ∀ {P : Value → Set ℓ} {h l r} (t : B23TreeP P h l r) → fromAll (toAll t) ≡ t
from-toAll  node₀ = refl
from-toAll (node₂ {h} {l} {r} x p t u) =
  trans
   (cong (DataC.toN B23TreePC)  -- [FAIL] manually un-normalised
    (cong inr
     (cong inl
      (cong (h ,_)
       (cong (l ,_)
        (cong (r ,_)
         (cong (x ,_)
          (cong (p ,_)
           (cong₂ _,_ (from-toAll t)
            (cong₂ _,_ (from-toAll u) refl))))))))))
   refl
from-toAll (node₃ {h} {l} {r} x p y q t u v) =
  trans
   (cong (DataC.toN B23TreePC)  -- [FAIL] manually un-normalised
    (cong inr
     (cong inr
      (cong inl
       (cong (h ,_)
        (cong (l ,_)
         (cong (r ,_)
          (cong (x ,_)
           (cong (p ,_)
            (cong (y ,_)
             (cong (q ,_)
              (cong₂ _,_ (from-toAll t)
               (cong₂ _,_ (from-toAll u)
                (cong₂ _,_ (from-toAll v) refl))))))))))))))
   refl

from-toAllC = genIndC from-toAllP from-toAll

-- to-fromAllP : IndP
-- to-fromAllP = remember-forget-inv toB23TreeC B23TreeAllC toAllC fromAllC (inl B23TreePFin)

-- [FAIL] too slow
-- unquoteDecl to-fromAll = defineInd to-fromAllP to-fromAll

-- [FAIL] manually case-split and elaborate-and-give but still too slow
-- to-fromAll : ∀ {P : Value → Set ℓ} {h l r} {t : B23Tree h l r} (allt : B23TreeAll P t)
--            → (toB23Tree (fromAll allt) , toAll (fromAll allt))
--            ≡ ((t , allt) ⦂ Σ[ t' ∈ B23Tree h l r ] B23TreeAll P t')
-- to-fromAll  node₀ = refl
-- to-fromAll (node₂ {h} {l} {r} {x} p {t} allt {u} allu) =
--   trans
--    (cong
--     (bimap (λ x → x) (DataC.toN B23TreeAllC))
--     (cong (bimap (λ x → x) inr)
--      (cong (bimap (λ x → x) inl)
--       (cong (bimap (λ x → x) (λ section → h , section))
--        (cong (bimap (λ x → x) (λ section → l , section))
--         (cong (bimap (λ x → x) (λ section → r , section))
--          (cong (bimap (λ x → x) (λ section → x , section))
--           (cong (bimap (λ x → x) (λ section → p , section))
--            (trans
--             (cong
--              (λ p →
--                 node₂ x (fst p) (toB23Tree (fromAll allu)) ,
--                 fst p ,
--                 snd p , toB23Tree (fromAll allu) , toAll (fromAll allu) , refl)
--              (to-fromAll allt))
--             (cong (bimap (λ x → x) (λ x → t , allt , x))
--              (trans
--               (cong (λ p → node₂ x t (fst p) , fst p , snd p , refl)
--                (to-fromAll allu))
--               refl)))))))))))
--    refl
-- to-fromAll (node₃ {h} {l} {r} {x} p {y} q {t} allt {u} allu {v} allv) =
--   trans
--    (cong
--     (bimap (λ x → x) (DataC.toN B23TreeAllC))
--     (cong (bimap (λ x → x) inr)
--      (cong (bimap (λ x → x) inr)
--       (cong (bimap (λ x → x) inl)
--        (cong (bimap (λ x → x) (λ section → h , section))
--         (cong (bimap (λ x → x) (λ section → l , section))
--          (cong (bimap (λ x → x) (λ section → r , section))
--           (cong (bimap (λ x → x) (λ section → x , section))
--            (cong (bimap (λ x → x) (λ section → p , section))
--             (cong (bimap (λ x → x) (λ section → y , section))
--              (cong (bimap (λ x → x) (λ section → q , section))
--               (trans
--                (cong
--                 (λ p →
--                    node₃ x y (fst p) (toB23Tree (fromAll allu))
--                    (toB23Tree (fromAll allv))
--                    ,
--                    fst p ,
--                    snd p ,
--                    toB23Tree (fromAll allu) ,
--                    toAll (fromAll allu) ,
--                    toB23Tree (fromAll allv) , toAll (fromAll allv) , refl)
--                 (to-fromAll allt))
--                (cong (bimap (λ x → x) (λ x → t , allt , x))
--                 (trans
--                  (cong
--                   (λ p →
--                      node₃ x y t (fst p) (toB23Tree (fromAll allv)) ,
--                      fst p ,
--                      snd p , toB23Tree (fromAll allv) , toAll (fromAll allv) , refl)
--                   (to-fromAll allu))
--                  (cong (bimap (λ x → x) (λ x → u , allu , x))
--                   (trans
--                    (cong (λ p → node₃ x y t u (fst p) , fst p , snd p , refl)
--                     (to-fromAll allv))
--                    refl))))))))))))))))
--    refl

-- to-fromAllC = genIndC to-fromAllP to-fromAll

-- Compare with hand-written version
to-fromAll : ∀ {P : Value → Set ℓ} {h l r} {t : B23Tree h l r} (allt : B23TreeAll P t)
           → (toB23Tree (fromAll allt) , toAll (fromAll allt))
           ≡ ((t , allt) ⦂ Σ[ t' ∈ B23Tree h l r ] B23TreeAll P t')
to-fromAll node₀ = refl
to-fromAll (node₂ _ allt allu) =
  cong₂ (λ (t' , allt') (u' , allu') → node₂ _ t' u' , node₂ _ allt' allu')
        (to-fromAll allt) (to-fromAll allu)
to-fromAll (node₃ _ _ allt allu allv) =
  cong₃ (λ (t' , allt') (u' , allu') (v' , allv') →
           node₃ _ _ t' u' v' , node₃ _ _ allt' allu' allv')
        (to-fromAll allt) (to-fromAll allu) (to-fromAll allv)

--------
-- Any predicate

B23TreeAnyD : DataD
B23TreeAnyD = ⌊ AnyOD B23TreeC B23TreeS ⌋ᵈ

-- unquoteDecl data B23TreeAny constructor c0 c1 c2 c3 c4 c5 c6 c7 = defineByDataD B23TreeAnyD B23TreeAny (c0 ∷ c1 ∷ c2 ∷ c3 ∷ c4 ∷ c5 ∷ c6 ∷ c7 ∷ [])
data B23TreeAny (P : Value → Set ℓ) : ∀ {h l r} → B23Tree h l r → Set ℓ where
  node₂-here   : ∀ {x   t u  } → P x → B23TreeAny P {suc h} {l} {r} (node₂ x   t u  )
  node₃-here₀  : ∀ {x y t u v} → P x → B23TreeAny P {suc h} {l} {r} (node₃ x y t u v)
  node₃-here₁  : ∀ {x y t u v} → P y → B23TreeAny P {suc h} {l} {r} (node₃ x y t u v)
  node₂-there₀ : ∀ {x   t u  } → B23TreeAny P t
               → B23TreeAny P {suc h} {l} {r} (node₂ x   t u  )
  node₂-there₁ : ∀ {x   t u  } → B23TreeAny P u
               → B23TreeAny P {suc h} {l} {r} (node₂ x   t u  )
  node₃-there₀ : ∀ {x y t u v} → B23TreeAny P t
               → B23TreeAny P {suc h} {l} {r} (node₃ x y t u v)
  node₃-there₁ : ∀ {x y t u v} → B23TreeAny P u
               → B23TreeAny P {suc h} {l} {r} (node₃ x y t u v)
  node₃-there₂ : ∀ {x y t u v} → B23TreeAny P v
               → B23TreeAny P {suc h} {l} {r} (node₃ x y t u v)

B23TreeAnyT = genDataT B23TreeAnyD B23TreeAny
B23TreeAnyC = genDataC B23TreeAnyD B23TreeAnyT

lookupB23TreeAnyP : FoldP
lookupB23TreeAnyP = lookupAny B23TreeC B23TreeS B23TreeAnyC

unquoteDecl lookupB23TreeAny = defineFold lookupB23TreeAnyP lookupB23TreeAny
-- lookupB23TreeAny :
--   ∀ {P : Value → Set ℓ} {h l r} {t : B23Tree h l r} → B23TreeAny P t → Σ Value P
-- lookupB23TreeAny (node₂-here   p) = _ , p
-- lookupB23TreeAny (node₃-here₀  p) = _ , p
-- lookupB23TreeAny (node₃-here₁  p) = _ , p
-- lookupB23TreeAny (node₂-there₀ i) = lookupB23TreeAny i
-- lookupB23TreeAny (node₂-there₁ i) = lookupB23TreeAny i
-- lookupB23TreeAny (node₃-there₀ i) = lookupB23TreeAny i
-- lookupB23TreeAny (node₃-there₁ i) = lookupB23TreeAny i
-- lookupB23TreeAny (node₃-there₂ i) = lookupB23TreeAny i

lookupB23TreeAnyC = genFoldC lookupB23TreeAnyP lookupB23TreeAny
