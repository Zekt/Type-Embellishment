{-# OPTIONS --safe --with-K #-}

module Examples.WithMacros.BST where

open import Prelude hiding (lookupAny)

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

variable h l r : ℕ

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

instance

  B23TreeC : Named (quote B23Tree) _
  unNamed B23TreeC = genDataC B23TreeD (genDataT B23TreeD B23Tree)
    where B23TreeD = genDataD B23Tree

  B23TreeS : SCᵈ (findDataD (quote B23Tree))
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

private
  B23TreePOD : DataOD (findDataD (quote B23Tree))
  B23TreePOD = PredOD (quote B23Tree)

instance B23TreePO = ⌈ B23TreePOD ⌉ᵈ

unquoteDecl data B23TreeP constructor b230 b231 b232 = defineByDataD ⌊ B23TreePOD ⌋ᵈ B23TreeP (b230 ∷ b231 ∷ b232 ∷ [])
--data B23TreeP (P : Value → Set ℓ) : Height → Value → Value → Set ℓ where
--
--  node₀ : ⦃ l ≤ r ⦄
--        → ----------------
--          B23TreeP P 0 l r
--
--  node₂ : (x : Value) → P x
--        → B23TreeP P h l x → B23TreeP P h x r
--        → -----------------------------------
--          B23TreeP P (suc h) l r
--
--  node₃ : (x : Value) → P x → (y : Value) → P y
--        → B23TreeP P h l x → B23TreeP P h x y → B23TreeP P h y r
--        → ------------------------------------------------------
--          B23TreeP P (suc h) l r

instance

  B23TreePC : Named (quote B23TreeP) _
  unNamed B23TreePC = genDataC ⌊ B23TreePOD ⌋ᵈ (genDataT ⌊ B23TreePOD ⌋ᵈ B23TreeP)

  B23TreePFin : Finitary ⌊ B23TreePOD ⌋ᵈ
  B23TreePFin = (tt ∷ tt ∷ tt ∷ [])
              ∷ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ refl ∷ refl ∷ [])
              ∷ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ refl ∷ refl ∷ refl ∷ []) ∷ []

private
  toB23TreeP : FoldP
  toB23TreeP = forget (quote B23TreeP) (quote B23Tree)

unquoteDecl toB23Tree = defineFold toB23TreeP toB23Tree
-- toB23Tree : ∀ {P : ℕ → Set ℓ} {h l r} → B23TreeP P h l r → B23Tree h l r
-- toB23Tree  node₀                 = node₀
-- toB23Tree (node₂ x p      t u  ) = node₂ x   (toB23Tree t) (toB23Tree u)
-- toB23Tree (node₃ x p y p' t u v) = node₃ x y (toB23Tree t) (toB23Tree u) (toB23Tree v)

instance toB23TreeC = genFoldC toB23TreeP toB23Tree

private
  B23TreeAllOD : DataOD (findDataD (quote B23TreeP))
  B23TreeAllOD = AllOD (quote B23Tree)

instance B23TreeAllO = ⌈ B23TreeAllOD ⌉ᵈ

unquoteDecl data B23TreeAll constructor b23all0 b23all1 b23all2 = defineByDataD ⌊ B23TreeAllOD ⌋ᵈ B23TreeAll (b23all0 ∷ b23all1 ∷ b23all2 ∷ [])
--data B23TreeAll (P : Value → Set ℓ) : ∀ {h l r} → B23Tree h l r → Set ℓ where
--
--  node₀ : ⦃ _ : l ≤ r ⦄
--        → ------------------------------
--          B23TreeAll P {0} {l} {r} node₀
--
--  node₂ : ∀ {x} → P x
--        → ∀ {t} → B23TreeAll P {h} {l} {x} t
--        → ∀ {u} → B23TreeAll P {h} {x} {r} u
--        → ----------------------------------
--          B23TreeAll P (node₂ x t u)
--
--  node₃ : ∀ {x} → P x → ∀ {y} → P y
--        → ∀ {t} → B23TreeAll P {h} {l} {x} t
--        → ∀ {u} → B23TreeAll P {h} {x} {y} u
--        → ∀ {v} → B23TreeAll P {h} {y} {r} v
--        → ----------------------------------
--          B23TreeAll P (node₃ x y t u v)

instance
  B23TreeAllC : Named (quote B23TreeAll) _
  unNamed B23TreeAllC = genDataC ⌊ B23TreeAllOD ⌋ᵈ (genDataT ⌊ B23TreeAllOD ⌋ᵈ B23TreeAll)

private
  fromAllP : FoldP
  fromAllP = forget (quote B23TreeAll) (quote B23TreeP)

unquoteDecl fromAll = defineFold fromAllP fromAll
-- fromAll : ∀ {P : Value → Set ℓ} {h l r} {t : B23Tree h l r}
--         → B23TreeAll P t → B23TreeP P h l r
-- fromAll  node₀            = node₀
-- fromAll (node₂ p   t u  ) = node₂ _ p     (fromAll t) (fromAll u)
-- fromAll (node₃ p q t u v) = node₃ _ p _ q (fromAll t) (fromAll u) (fromAll v)

instance fromAllC = genFoldC fromAllP fromAll

private
  toAllP : IndP
  toAllP = remember (quote B23TreeAll)

unquoteDecl toAll = defineInd toAllP toAll
-- toAll : ∀ {P : Value → Set ℓ} {h l r} (t : B23TreeP P h l r) → B23TreeAll P (toB23Tree t)
-- toAll  node₀                = node₀
-- toAll (node₂ x p     t u  ) = node₂ p   (toAll t) (toAll u)
-- toAll (node₃ x p y q t u v) = node₃ p q (toAll t) (toAll u) (toAll v)

instance toAllC = genIndC toAllP toAll

--private
--  from-toAllP : IndP
--  from-toAllP = forget-remember-inv (quote B23TreeAll) (quote B23TreeP) (inl it)
--
--unquoteDecl from-toAll = defineInd from-toAllP from-toAll
-- from-toAll : ∀ {P : Value → Set ℓ} {h l r} (t : B23TreeP P h l r) → fromAll (toAll t) ≡ t
-- from-toAll  node₀ = refl
-- from-toAll (node₂ x p t u) =
--   trans'
--     (cong (node₂ x p (fromAll (toAll t))) (from-toAll u))
--     (cong (λ n' → node₂ x p n' u) (from-toAll t))
-- from-toAll (node₃ x p y q t u v) =
--   trans'
--    (cong
--     (node₃ x p y q (fromAll (toAll t)) (fromAll (toAll u)))
--     (from-toAll v))
--    (trans'
--     (cong (λ n' → node₃ x p y q (fromAll (toAll t)) n' v)
--      (from-toAll u))
--     (cong (λ n' → node₃ x p y q n' u v) (from-toAll t)))

--instance from-toAllC = genIndC from-toAllP from-toAll
--
--private
--  to-fromAllP : IndP
--  to-fromAllP = remember-forget-inv (quote B23TreeAll) (quote B23TreeP) (inl it)
--
--unquoteDecl to-fromAll = defineInd to-fromAllP to-fromAll
-- to-fromAll : ∀ {P : Value → Set ℓ} {h l r} {t : B23Tree h l r} (allt : B23TreeAll P t)
--            → (toB23Tree (fromAll allt) , toAll (fromAll allt))
--            ≡ ((t , allt) ⦂ Σ[ t' ∈ B23Tree h l r ] B23TreeAll P t')
-- to-fromAll  node₀ = refl
-- to-fromAll (node₂ {h} {l} {r} {x} p {t} allt {u} allu) =
--   trans
--    (cong
--     (bimap (λ x → x) (DataC.toN (findDataC (quote B23TreeAll))))
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
--     (bimap (λ x → x) (DataC.toN (findDataC (quote B23TreeAll))))
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

--instance to-fromAllC = genIndC to-fromAllP to-fromAll

--------
-- Any predicate

private
  B23TreeAnyD : DataD
  B23TreeAnyD = AnyD (quote B23Tree)

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

instance
  B23TreeAnyC : Named (quote B23TreeAny) _
  unNamed B23TreeAnyC = genDataC B23TreeAnyD B23TreeAnyT
    where B23TreeAnyT = genDataT B23TreeAnyD B23TreeAny

private
  lookupB23TreeAnyP : FoldP
  lookupB23TreeAnyP = lookupAny (quote B23Tree)

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

instance lookupB23TreeAnyC = genFoldC lookupB23TreeAnyP lookupB23TreeAny
