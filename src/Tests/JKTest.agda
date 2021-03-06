{-# OPTIONS --safe --with-K #-}

module Tests.JKTest where

open import Prelude
open import Generics.Telescope
open import Generics.Description
open import Generics.Description.FixedPoint
open import Generics.Algebra
open import Generics.Recursion
open import Generics.RecursionScheme
open import Generics.Ornament
open import Generics.Ornament.Description
open import Generics.Ornament.Algebraic
open import Generics.Ornament.Algebraic.Isomorphism
open import Generics.SimpleContainer
open import Generics.SimpleContainer.All
open import Generics.SimpleContainer.Any
open import Examples.Acc

open import Generics.Reflection

record PFoldP (D : PDataD) : Setω where
  field
    {plevel} {clevel} : Level
    Param   : Tel plevel
    param   : ⟦ Param ⟧ᵗ → ⟦ D .PDataD.Param ⟧ᵗ
    Carrier : ∀ ps → ⟦ D .PDataD.Index (param ps) ⟧ᵗ → Set clevel
    applyP  : ∀ ps → Algᶜˢ (D .PDataD.applyP (param ps)) (Carrier ps)

record FoldP' : Setω where field
  {Desc}   : DataD; {Native} : DataT Desc
  Con      : DataC Desc Native
  #levels  : ℕ
  level    : Level ^ #levels → Level ^ (Desc .DataD.#levels)
  applyL   : ∀ ℓs → PFoldP (Desc .DataD.applyL (level ℓs))

FoldT' : FoldP' → Setω
FoldT' F = ∀ ℓs ps {is} → let open FoldP' F; open PFoldP (F .FoldP'.applyL ℓs) in
           Native (level ℓs) (param ps) is → Carrier ps is

record FoldC' (F : FoldP') (f : FoldT' F) : Setω where field
  equation :  ∀ {ℓs ps is} → let open FoldP' F; open PFoldP (F .FoldP'.applyL ℓs) in
              (ns : ⟦ Desc ⟧ᵈ (Native (level ℓs) (param ps)) is) →
              f ℓs ps (Con .DataC.toN ns) ≡ applyP ps (fmapᵈ Desc (f ℓs ps) ns)

FoldNT' : (F : FoldP') (ℓs : Level ^ (F .FoldP'.#levels)) → Set _
FoldNT' F ℓs = let open FoldP' F; open PFoldP (F .FoldP'.applyL ℓs) in
  Curriedᵗ Param (constTelInfo visible) λ ps → Curriedᵗ (Desc .DataD.applyL (level ℓs) .PDataD.Index (param ps)) (constTelInfo visible) λ is →
  Native (level ℓs) (param ps) is → Carrier ps is

fold-base' : (F : FoldP') → ∀ {ℓs} → FoldNT' F ℓs → FoldNT' F ℓs
fold-base' F {ℓs} rec = let open FoldP' F; open PFoldP (F .FoldP'.applyL ℓs) in
  curryᵗ λ ps → curryᵗ λ is →
  applyP ps {is} ∘ fmapᵈ Desc (λ {is} → uncurryᵗ (uncurryᵗ rec ps) is) ∘ Con .DataC.fromN

foldAccP : FoldP'
foldAccP = record
  { Con      = findDataC (quote Acc)
  ; #levels  = 3
  ; level    = snd
  ; applyL   = λ (ℓ'' , ℓ , ℓ' , _) → record
    { Param   = [ A ∶ Set ℓ ] [ R ∶ (A → A → Set ℓ') ] [ P ∶ (A → Set ℓ'') ] [ p ∶ (∀ x → (∀ y → R y x → P y) → P x) ] []
    ; param   = λ (A , R , P , p , _) → A , R , tt
    ; Carrier = λ (A , R , P , p , _) (x , _) → P x
    ; applyP  = λ { (A , R , P , p , _) (inl (x , ps , refl)) → p x ps } } }

foldAcc' : {ℓs : Σ Level (λ _ → Σ Level (λ _ → Σ Level (λ _ → ⊤)))}
  (a : Set (fst (snd ℓs))) (a₁ : a → a → Set (fst (snd (snd ℓs))))
  (a₂ : a → Set (fst ℓs))
  (a₃ : (x : a) → ((y : a) → a₁ y x → a₂ y) → a₂ x) (a₄ : a) →
  Acc a₁ a₄ → a₂ a₄
foldAcc' A R P p x (acc as) = p x (λ a a₁ → foldAcc' A R P p a (as a a₁))

foldAccT : FoldT' foldAccP
foldAccT _ (A , R , P , p , _) {x , _} = foldAcc' A R P p x

-- -- META
-- NatD : DataD
-- NatD = genDataD ℕ
-- {-
-- NatD = record
--   { #levels = 0
--   ; applyL  = λ _ → record
--       { alevel = 0ℓ
--       ; Param  = []
--       ; Index  = λ _ → []
--       ; applyP = λ _ → ι tt ∷ ρ (ι tt) (ι tt) ∷ [] } }
-- -}

-- -- META
-- -- ℕ-wrapper : DataT NatD
-- ℕ-wrapper = genDataT NatD ℕ -- _ _ _ = ℕ

-- -- META
-- -- NatC : DataC NatD ℕ-wrapper
-- NatC = genDataC NatD ℕ-wrapper

-- {-
-- NatC = record
--   { toN   = λ { (inl           refl  ) → zero
--               ; (inr (inl (n , refl))) → suc n }
--   ; fromN = λ {  zero   → inl           refl
--               ; (suc n) → inr (inl (n , refl)) }
--   ; fromN-toN = λ { (inl           refl  ) → refl
--                   ; (inr (inl (n , refl))) → refl }
--   ; toN-fromN = λ {  zero   → refl
--                   ; (suc n) → refl } }
-- -}

-- -- USER (specialising a generic library component)
-- foldℕP : FoldP
-- foldℕP = fold-operator NatC

-- -- META
-- foldℕ : {ℓ : Level} (a : Set ℓ) (a₁ : a) (a₂ : a → a) → ℕ → a
-- foldℕ X z s  zero   = z
-- foldℕ X z s (suc n) = s (foldℕ X z s n)
-- -- foldℕ X z s  zero   = {! fold-base foldℕP foldℕ X z s zero    !}
-- -- foldℕ X z s (suc n) = {! fold-base foldℕP foldℕ X z s (suc n) !}

-- -- USER (changing the form)
-- -- foldℕ : ∀ {ℓ} {X : Set ℓ} → (X → X) → X → ℕ → X
-- -- foldℕ s z  zero   = z
-- -- foldℕ s z (suc n) = s (foldℕ s z n)

-- -- META
-- foldℕ-wrapper : FoldT foldℕP
-- foldℕ-wrapper = genFoldT foldℕP foldℕ -- _ (_ , X , z , s , _) = foldℕ X z s

-- -- foldℕC : FoldC foldℕP foldℕ-wrapper
-- foldℕC = genFoldC' foldℕP foldℕ-wrapper

-- {-
-- FoldC.equation foldℕC (inl           refl  ) = refl
-- FoldC.equation foldℕC (inr (inl (_ , refl))) = refl
-- -}

-- -- META (specialising ‘fold-fusion NatC foldℕC’)
-- unquoteDecl foldℕ-fusion = defineInd (fold-fusion NatC foldℕC) foldℕ-fusion
-- {-
-- foldℕ-fusion : {ℓs : Σ Level (λ _ → Σ Level (λ _ → ⊤))} (a : Set (fst ℓs))
--   (a₁ : Set (fst (snd ℓs))) (a₂ : a → a₁) (a₃ : a) (a₄ : a → a)
--   (a₅ : a₁) (a₆ : a₁ → a₁) (a₇ : a₂ a₃ ≡ a₅)
--   (a₈ : (xs : a) (ys : a₁) → ys ≡ a₂ xs → a₂ (a₄ xs) ≡ a₆ ys)
--   (n : ℕ) →
--   a₂ (foldℕ a a₃ a₄ n) ≡ foldℕ a₁ a₅ a₆ n
-- foldℕ-fusion a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ zero = trans a₇ refl
-- foldℕ-fusion a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ (suc n) =
--   trans
--    (a₈ (foldℕ a a₃ a₄ n) (foldℕ a₁ a₅ a₆ n)
--     (sym (foldℕ-fusion a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ n)))
--    refl
-- -}

-- -- USER (specialising a generic library component)
-- indℕP : IndP
-- indℕP = ind-operator NatC

-- -- META
-- {- generated by defineInd indℕP
-- indℕ : {ℓ : Level} (a : ℕ → Set ℓ)
--        (a₁ : a 0) (a₂ : (ns : ℕ) → a ns → a (suc ns)) (n : ℕ) → a n
-- indℕ P z s  zero   = z
-- indℕ P z s (suc n) = s n (indℕ P z s n)
-- -}

-- -- USER (changing the form)
-- indℕ : ∀ {ℓ} (P : ℕ → Set ℓ) → P zero → (∀ n → P n → P (suc n)) → ∀ n → P n
-- indℕ P z s  zero   = z
-- indℕ P z s (suc n) = s n (indℕ P z s n)

-- -- META
-- indℕ-wrapper : IndT indℕP
-- indℕ-wrapper = genIndT indℕP indℕ --  _ (_ , P , z , s , _) = indℕ P z s

-- -- indℕ-is-ind : IndC indℕP indℕ-wrapper
-- indℕ-is-ind = genIndC' indℕP indℕ-wrapper
-- {-
-- IndC.equation indℕ-is-ind (inl           refl  ) = refl
-- IndC.equation indℕ-is-ind (inr (inl (_ , refl))) = refl
-- -}

-- -- META
-- ListD : DataD
-- ListD = genDataD List
-- {-
-- ListD = record
--   { #levels = 1
--   ; applyL  = λ ℓs → let (ℓ , _) = ℓs in record
--       { alevel = ℓ
-- --      ; level-inequality = refl
--       ; Param  = [ A ∶ Set ℓ ] []
--       ; Index  = λ _ → []
--       ; applyP = λ ps → let (A , _) = ps
--                         in (ι tt)
--                          ∷ (σ A λ _ → ρ (ι tt) (ι tt))
--                          ∷ [] } }
-- -}

-- -- META
-- List-wrapper : DataT ListD
-- List-wrapper = genDataT ListD List -- (ℓ , _) (A , _) _ = List A

-- -- META
-- ListC : DataC ListD List-wrapper
-- ListC = genDataC ListD List-wrapper
-- {-
-- ListC = record
--   { toN   = λ { (inl                refl  ) → []
--               ; (inr (inl (a , as , refl))) → a ∷ as }
--   ; fromN = λ { []       → inl                refl
--               ; (a ∷ as) → inr (inl (a , as , refl)) }
--   ; fromN-toN = λ { (inl                refl  ) → refl
--                   ; (inr (inl (a , as , refl))) → refl }
--   ; toN-fromN = λ { []       → refl
--                   ; (a ∷ as) → refl } }
-- -}

-- -- USER
-- ListD/NatD : DataO ListD NatD
-- ListD/NatD = record
--   { level  = λ _ → tt
--   ; applyL = λ ℓs → let (ℓ , _) = ℓs in record
--       { param  = λ _ → tt
--       ; index  = λ _ _ → tt
--       ; applyP = λ _ → ι ∷ ∺ (Δ λ _ → ρ ι ι) ∷ ∺ [] } }

-- -- USER
-- length'P : FoldP
-- length'P = forget ListC NatC ListD/NatD

-- -- META & USER (cosmetic changes)
-- length' : {A : Set ℓ} → List A → ℕ
-- length' []       = 0
-- length' (x ∷ xs) = suc (length' xs)
-- -- length' : {! FoldNT lengthP !}
-- -- length' A []       = {! fold-base length'P length' A []       !}
-- -- length' A (x ∷ xs) = {! fold-base length'P length' A (x ∷ xs) !}

-- -- META
-- length'-wrapper : FoldT length'P
-- length'-wrapper = genFoldT length'P length' -- _ A = length'

-- -- length'C : FoldC length'P length'-wrapper
-- length'C = genFoldC' length'P length'-wrapper
-- {-
-- FoldC.equation length'C (inl               refl  ) = refl
-- FoldC.equation length'C (inr (inl (_ , _ , refl))) = refl
-- -}

-- -- USER
-- VecOD : DataOD ListD
-- VecOD = AlgOD length'P

-- VecD : DataD
-- VecD = ⌊ VecOD ⌋ᵈ

-- -- META & USER
-- data Vec (A : Set ℓ) : ℕ → Set ℓ where
--   []  : Vec A zero
--   _∷_ : A → {n : ℕ} → Vec A n → Vec A (suc n)

-- -- META
-- Vec-wrapper : DataT VecD
-- Vec-wrapper = genDataT VecD Vec -- (ℓ , _) (A , _) (_ , n , _) = Vec A n

-- VecC : DataC VecD Vec-wrapper
-- VecC = record
--   { toN   = λ { (inl                    refl  ) → []
--               ; (inr (inl (a , n , as , refl))) → a ∷ as }
--   ; fromN = λ { []       → inl                    refl
--               ; (a ∷ as) → inr (inl (a , _ , as , refl)) }
--   ; fromN-toN = λ { (inl                    refl  ) → refl
--                   ; (inr (inl (a , n , as , refl))) → refl }
--   ; toN-fromN = λ { []       → refl
--                   ; (a ∷ as) → refl } }

-- -- USER
-- Vec-rememberP : IndP
-- Vec-rememberP = remember length'C VecC

-- -- META & USER
-- Vec-remember : {A : Set ℓ} (as : List A) → Vec A (length' as)
-- Vec-remember []       = []
-- Vec-remember (x ∷ xs) = x ∷ Vec-remember xs
-- -- Vec-remember : {! IndNT Vec-rememberP !}
-- -- Vec-remember A []       = {! ind-base Vec-rememberP Vec-remember A []       !}
-- -- Vec-remember A (x ∷ xs) = {! ind-base Vec-rememberP Vec-remember A (x ∷ xs) !}

-- -- META
-- Vec-remember-wrapper : IndT Vec-rememberP
-- Vec-remember-wrapper = genIndT Vec-rememberP Vec-remember -- _ (A , _) = Vec-remember

-- -- Vec-rememberC : IndC Vec-rememberP Vec-remember-wrapper
-- Vec-rememberC = genIndC' Vec-rememberP Vec-remember-wrapper
-- -- IndC.equation Vec-rememberC (inl               refl  ) = refl
-- -- IndC.equation Vec-rememberC (inr (inl (_ , _ , refl))) = refl

-- -- USER
-- fromVecP : FoldP
-- fromVecP = forget VecC ListC ⌈ VecOD ⌉ᵈ

-- -- META & USER
-- fromVec : {A : Set ℓ} {n : ℕ} → Vec A n → List A
-- fromVec []       = []
-- fromVec (x ∷ xs) = x ∷ fromVec xs

-- -- META
-- fromVec-wrapper : FoldT fromVecP
-- fromVec-wrapper = genFoldT fromVecP fromVec -- _ (A , _) = fromVec

-- -- fromVecC : FoldC fromVecP fromVec-wrapper
-- fromVecC = genFoldC' fromVecP fromVec-wrapper
-- {-
-- FoldC.equation fromVecC (inl                   refl  ) = refl
-- FoldC.equation fromVecC (inr (inl (_ , _ , _ , refl))) = refl
-- -}

-- -- USER
-- inverseP : IndP
-- inverseP = remember-forget-inv length'C VecC Vec-rememberC fromVecC
--              (inl (λ ℓs → [] ∷ (tt ∷ refl ∷ []) ∷ []))

-- -- META & USER
-- inverse : {A : Set ℓ} {n : ℕ} (xs : Vec A n)
--         → (length' (fromVec xs) , Vec-remember (fromVec xs))
--         ≡ ((n , xs) ⦂ Σ ℕ (Vec A))  -- manual type annotation
--                                     -- (Agda normalisation may not preserve types!)
-- inverse []       = refl
-- inverse (x ∷ xs) =
--   trans
--    (cong
--     (bimap (λ x → x) (DataC.toN VecC))  -- requires manual definition-folding
--     (cong (bimap (λ x → x) inr)
--      (cong (bimap (λ x → x) inl)
--       (cong (bimap (λ x → x) (λ section → x , section))
--        (trans
--         (cong (λ p → suc (fst p) , fst p , snd p , refl) (inverse xs))
--         refl)))))
--    refl

-- -- META
-- inverse-wrapper : IndT inverseP
-- inverse-wrapper = genIndT inverseP inverse -- _ (A , _) = inverse

-- open import Utils.Reflection

-- -- inverseC : IndC inverseP inverse-wrapper
-- inverseC = genIndC' inverseP inverse-wrapper
-- {-
-- IndC.equation inverseC (inl                   refl  ) = refl
-- IndC.equation inverseC (inr (inl (_ , _ , _ , refl))) = refl
-- -}

-- VecSC : SCᵈ VecD
-- VecSC = λ _ → record
--   { El  = λ (A , _) → A
--   ; pos = [] ∷ (true ∷ false ∷ tt ∷ []) ∷ []
--   ; coe = λ _ → lift tt ,ωω (refl ,ωω λ _ _ → lift tt) ,ωω lift tt }

-- WD : DataD
-- WD = record
--   { #levels = 2
--   ; applyL  = λ ℓs → let (ℓ , ℓ' , _) = ℓs in record
--       { alevel = ℓ ⊔ ℓ'
--       ; Param  = [ A ∶ Set ℓ ] [ _ ∶ (A → Set ℓ') ] []
--       ; Index  = λ _ → []
--       ; applyP = λ ps → let (A , B , _) = ps
--                        in (σ A λ a → ρ (π (B a) λ _ → ι tt) (ι tt))
--                         ∷ [] } }

-- -- data IEqW {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} : W A B → W A B → Set (ℓ ⊔ ℓ') where
-- --   sup : (a : A) → {ws : B a → W A B × W A B}
-- --                 → ((b : B a) → IEqW (fst (ws b)) (snd (ws b)))
-- --                 → IEqW (sup a (fst ∘ ws)) (sup a (snd ∘ ws))

-- -- data SW {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') : W A B → Set (ℓ ⊔ ℓ') where
-- --   sup : (a : A) → {w : B a → W A B} → ((b : B a) → SW A B (w b)) → SW A B (sup a w)

-- -- rememberSW : {A : Set ℓ} {B : A → Set ℓ'} (w : W A B) → SW A B w
-- -- rememberSW (sup a w) = sup a λ b → rememberSW (w b)

-- -- forgetSW : {A : Set ℓ} {B : A → Set ℓ'} {w : W A B} → SW A B w → W A B
-- -- forgetSW (sup a s) = sup a λ b → forgetSW (s b)

-- -- forget-remember-invSW : {A : Set ℓ} {B : A → Set ℓ'} (w : W A B)
-- --                       → IEqW (forgetSW (rememberSW w)) w
-- -- forget-remember-invSW (sup a w) =
-- --   sup a {λ b → forgetSW (rememberSW (w b)) , w b} λ b → forget-remember-invSW (w b)

-- -- w₀ w₁ : W Bool λ b → if b then Bool else ⊥
-- -- w₀ = sup true λ _ → sup false λ ()
-- -- w₁ = sup true λ { false → sup false λ (); true → sup false λ () }

-- -- w₀≡w₁ : w₀ ≡ w₁
-- -- w₀≡w₁ = {! refl !}

-- -- IEqW-w₀-w₁ : IEqW w₀ w₁
-- -- IEqW-w₀-w₁ = sup true (λ { false → sup false λ (); true → sup false λ () })

-- -- fromIEqW : FunExt → {A : Set ℓ} {B : A → Set ℓ'} {x y : W A B} → IEqW x y → x ≡ y
-- -- fromIEqW funext (sup a e) = cong (sup a) (funext λ b → fromIEqW funext (e b))

-- -- data BW (A : Set) (B : A → Set) (f : {a : A} → (B a → ℕ) → ℕ) : ℕ → Set where
-- --   sup : (a : A) → {ns : B a → ℕ} → ((b : B a) → BW A B f (ns b)) → BW A B f (f ns)

-- -- data IEqBW {A : Set} {B : A → Set} {f : {a : A} → (B a → ℕ) → ℕ} :
-- --   (m n : ℕ) → BW A B f m → BW A B f n → Set where
-- --   sup : (a : A) → {ms ns : B a → ℕ}
-- --         {x : (b : B a) → BW A B f (ms b)} {y : (b : B a) → BW A B f (ns b)}
-- --       → ((b : B a) → IEqBW (ms b) (ns b) (x b) (y b))
-- --       → IEqBW (f ms) (f ns) (sup a x) (sup a y)

-- -- module _ {A : Set} {B : A → Set} {f : {a : A} → (B a → ℕ) → ℕ} where

-- --   foldW : W A B → ℕ
-- --   foldW (sup a w) = f (λ b → foldW (w b))

-- --   forgetBW : {n : ℕ} → BW A B f n → W A B
-- --   forgetBW (sup a w) = sup a (λ b → forgetBW (w b))

-- --   rememberBW : (w : W A B) → BW A B f (foldW w)
-- --   rememberBW (sup a w) = sup a (λ b → rememberBW (w b))

-- --   remember-forget-invBW : (n : ℕ) (w : BW A B f n)
-- --                         → IEqBW (foldW (forgetBW w)) n (rememberBW (forgetBW w)) w
-- --   remember-forget-invBW .(f _) (sup a w) =
-- --     sup a {λ b → foldW (forgetBW (w b))} λ b → remember-forget-invBW _ (w b)

-- -- PointwiseD : DataD
-- -- PointwiseD = record
-- --   { #levels = 3
-- --   ; applyL  = λ ℓs → let (ℓᵃ , ℓᵇ , ℓʳ , _) = ℓs in record
-- --       { alevel = ℓᵃ ⊔ ℓᵇ ⊔ ℓʳ
-- -- --       ; level-pre-fixed-point = refl
-- --       ; Param  = [ A ∶ Set ℓᵃ ] [ B ∶ Set ℓᵇ ] [ _ ∶ (A → B → Set ℓʳ) ] []
-- --       ; Index  = λ p → let (A , B , R , _) = p
-- --                        in [ _ ∶ List A ] [ _ ∶ List B ] []
-- --       ; applyP = λ p → let (A , B , R , _) = p
-- --                        in (ι ([] , [] , tt))
-- --                         ∷ (σ  A       λ a  →
-- --                            σ  B       λ b  →
-- --                            σ (R a b ) λ _  →
-- --                            σ (List A) λ as →
-- --                            σ (List B) λ bs →
-- --                            ρ (ι (as , bs , tt))
-- --                           (ι (a ∷ as , b ∷ bs , tt)))
-- --                         ∷ [] } }

-- -- mutual

-- --   data Even : ℕ → Set where
-- --     zero : Even zero
-- --     suc  : ∀ {n} → Odd n → Even (suc n)

-- --   data Odd : ℕ → Set where
-- --     suc : ∀ {n} → Even n → Odd (suc n)

-- -- parity : Algᵈ ⌊ SNatOD ⌋ᵈ λ _ _ _ → Bool
-- -- parity (inl               refl  ) = false
-- -- parity (inr (inl (_ , b , refl))) = not b

-- -- PNatOD : DataOD ⌊ SNatOD ⌋ᵈ
-- -- PNatOD = algODᵈ ⌊ SNatOD ⌋ᵈ (λ _ _ → algebra _ parity)

-- -- data PNat : ℕ → Bool → Set where
-- --   zero : PNat zero false
-- --   suc  : ∀ {n b} → PNat n b → PNat (suc n) (not b)

-- -- ParityOD : DataOD ⌊ PNatOD ⌋ᵈ
-- -- ParityOD = record
-- --   { #levels = 0
-- --   ; LevelO  = ε
-- --   ; applyL  = λ _ → record
-- --       { alevel  = lzero
-- -- --       ; level-pre-fixed-point = refl
-- --       ; ParamOD = ε
-- --       ; IndexOD = λ _ → ε
-- --       ; applyP  = λ _ → (ι _ refl)
-- --                     ∷ ∺ (σ λ n → ∇ false (ρ (ι _ refl) (ι _ refl)))
-- --                     ∷   (σ λ n → ∇ true  (ρ (ι _ refl) (ι _ refl)))
-- --                     ∷ ∺ [] } }

-- -- data Parity : ℕ → Bool → Set where
-- --   zero : Parity zero false
-- --   suc₀ : ∀ {n} → Parity n false → Parity (suc n) true
-- --   suc₁ : ∀ {n} → Parity n true  → Parity (suc n) false

-- -- Even' Odd' : ℕ → Set
-- -- Even' n = Parity n false
-- -- Odd'  n = Parity n true

-- -- VecD/NatD : SetO VecD NatD
-- -- VecD/NatD = record
-- --   { param = λ _ → tt
-- --   ; index = λ _ _ → tt
-- --   ; applyP   = λ { (_ , A) → ι refl
-- --                       ∷ ◂ Δ (λ a → Δ λ n → ρ (ι refl) (ι refl))
-- --                       ∷ ◂ [] } }

-- -- ListD : PDataD {_} {lzero}
-- -- ListD = record
-- --   { Param = [] ▷ (λ _ → Set)
-- --   ; Index = λ _ → []
-- --   ; Desc  = λ { (_ , A) → ι tt
-- --                         ∷ σ A (λ _ → ρ (ι tt) (ι tt))
-- --                         ∷ [] } }

-- -- BinOD : SetOD ListD
-- -- BinOD = record
-- --   { Param = []
-- --   ; param = λ _ → tt , Bool
-- --   ; Index = λ _ → []
-- --   ; index = λ _ _ → tt
-- --   ; applyP   = λ _ → ι tt refl
-- --               ∷ ◂ ∇ false (ρ (ι tt refl) (ι tt refl))
-- --               ∷   ∇ true  (ρ (ι tt refl) (ι tt refl))
-- --               ∷ ◂ [] }

-- -- VecD' : ⟦ [] ▷ (λ _ → Set) ⟧ᵗ → PDataD {lsuc lzero}
-- -- VecD' (_ , A) = record
-- --   { Param = []
-- --   ; Index = λ _ → [] ▷ (λ _ → ℕ)
-- --   ; Desc  = λ _ → ι (tt , zero)
-- --                 ∷ σ A (λ _ → σ ℕ λ n → ρ (ι (tt , n)) (ι (tt , suc n)))
-- --                 ∷ [] }

-- -- open import Data.Vec

-- -- toVec' : {p : ⟦ [] ▷ (λ _ → Set) ⟧ᵗ} {i : ⟦ [] ▷ (λ _ → ℕ) ⟧ᵗ}
-- --        → ⟦ VecD' p ⟧ˢ (Vec (snd p) ∘ snd) i → Vec (snd p) (snd i)
-- -- toVec' (inl                    refl  ) = []
-- -- toVec' (inr (inl (a , _ , as , refl))) = a ∷ as

-- -- fromVec' : {p : ⟦ [] ▷ (λ _ → Set) ⟧ᵗ} {i : ⟦ [] ▷ (λ _ → ℕ) ⟧ᵗ}
-- --          → Vec (snd p) (snd i) → ⟦ VecD' p ⟧ˢ (Vec (snd p) ∘ snd) i
-- -- fromVec' []       = inl                    refl
-- -- fromVec' (a ∷ as) = inr (inl (a , _ , as , refl))

-- -- VecParamO : (p q : ⟦ [] ▷ (λ _ → Set) ⟧ᵗ)
-- --           → (snd p → snd q)
-- --          → SetO (VecD' p) (VecD' q)
-- -- VecParamO (_ , A) (_ , B) f = record
-- --   { param = λ _ → tt
-- --   ; index = λ _ i → i
-- --   ; applyP   = λ _ → ι refl
-- --               ∷ ◂ Δ (λ a → ∇ (f a) (σ λ n → ρ (ι refl) (ι refl)))
-- --               ∷ ◂ [] }

-- -- vmap-base : {A B : Set} → (A → B)
-- --           → ({n : ℕ} → Vec A n → Vec B n)
-- --           → ({n : ℕ} → Vec A n → Vec B n)
-- -- vmap-base {A} {B} f rec =
-- --   toVec' ∘ eraseˢ (VecParamO (tt , A) (tt , B) f) ∘ fmapˢ (VecD' (tt , A)) rec ∘ fromVec'

-- -- vmap : {A B : Set} → (A → B) → {n : ℕ} → Vec A n → Vec B n
-- -- vmap f []       = {! vmap-base f (vmap f) [] !}
-- -- vmap f (x ∷ xs) = {! vmap-base f (vmap f) (x ∷ xs) !}
