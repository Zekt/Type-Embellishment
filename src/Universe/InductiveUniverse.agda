{-# OPTIONS --allow-unsolved-metas #-}
--{-# OPTIONS --safe #-}

module Universe.InductiveUniverse where

open import Level using (Lift)
open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality


record Unit {ℓ} : Set ℓ where
  constructor tt

data Empty {ℓ} : Set ℓ where

data Sum {ℓ₀ ℓ₁} (A : Set ℓ₀) (B : Set ℓ₁) : Set (ℓ₀ ⊔ ℓ₁) where
  inl : A → Sum A B
  inr : B → Sum A B

subst : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y : A} → x ≡ y → P x → P y
subst P refl p = p


mutual

  data Tel {ℓᵇ} (B : Set ℓᵇ) ℓ : Set (lsuc (ℓᵇ ⊔ ℓ)) where
    nil  : Tel B ℓ
    snoc : (T : Tel B ℓ) (A : Σ B ⟦ T ⟧ᵗ → Set ℓ) → Tel B ℓ

  ⟦_⟧ᵗ : ∀ {ℓᵇ ℓ} {B : Set ℓᵇ} → Tel B ℓ → B → Set ℓ
  ⟦ nil      ⟧ᵗ _ = Unit
  ⟦ snoc T A ⟧ᵗ b = Σ (⟦ T ⟧ᵗ b) (λ t → A (b , t))

Tel₀ : ∀ ℓ → Set (lsuc ℓ)
Tel₀ = Tel (Unit {lzero})

⟦_⟧ᵗ⁰ : ∀ {ℓ} → Tel₀ ℓ → Set ℓ
⟦ T ⟧ᵗ⁰ = ⟦ T ⟧ᵗ tt

module _ {ℓᵖ ℓⁱ} (P : Tel₀ ℓᵖ) (I : Tel ⟦ P ⟧ᵗ⁰ ℓⁱ) where

  private variable T : Tel ⟦ P ⟧ᵗ⁰ ℓⁱ

  data ConD : Tel ⟦ P ⟧ᵗ⁰ ℓⁱ → Set (lsuc (ℓᵖ ⊔ ℓⁱ)) where
    ι : (i : (e : Σ ⟦ P ⟧ᵗ⁰ ⟦ T ⟧ᵗ) → ⟦ I ⟧ᵗ (fst e)) → ConD T
    ρ : (U : Tel (Σ ⟦ P ⟧ᵗ⁰ ⟦ T ⟧ᵗ) ℓⁱ)
        (i : (e : Σ (Σ ⟦ P ⟧ᵗ⁰ ⟦ T ⟧ᵗ) ⟦ U ⟧ᵗ) → ⟦ I ⟧ᵗ (fst (fst e)))
        (C : ConD T) → ConD T
    σ : (A : Σ ⟦ P ⟧ᵗ⁰ ⟦ T ⟧ᵗ → Set ℓⁱ) (C : ConD (snoc T A)) → ConD T

  data SetD : Set (lsuc (ℓᵖ ⊔ ℓⁱ)) where
    nil  : SetD
    cons : (C : ConD nil) (Cs : SetD) → SetD

module _ {ℓᵖ ℓⁱ} {P : Tel₀ ℓᵖ} {I : Tel ⟦ P ⟧ᵗ⁰ ℓⁱ} where

  ⟦_⟧ᶜ : {T : Tel ⟦ P ⟧ᵗ⁰ ℓⁱ} → ConD P I T → (e : Σ ⟦ P ⟧ᵗ⁰ ⟦ T ⟧ᵗ)
       → (⟦ I ⟧ᵗ (fst e) → Set ℓⁱ) → (⟦ I ⟧ᵗ (fst e) → Set ℓⁱ)
  ⟦ ι   i   ⟧ᶜ e       X j = i e ≡ j
  ⟦ ρ U i C ⟧ᶜ e       X j = Σ ((u : ⟦ U ⟧ᵗ e) → X (i (e , u))) λ _ → ⟦ C ⟧ᶜ e X j
  ⟦ σ A   C ⟧ᶜ (p , t) X j = Σ (A (p , t)) λ a → ⟦ C ⟧ᶜ (p , (t , a)) X j

  ⟦_⟧ˢ : SetD P I → (p : ⟦ P ⟧ᵗ⁰) → (⟦ I ⟧ᵗ p → Set ℓⁱ) → (⟦ I ⟧ᵗ p → Set ℓⁱ)
  ⟦ nil       ⟧ˢ p X i = Empty
  ⟦ cons C Cs ⟧ˢ p X i = Sum (⟦ C ⟧ᶜ (p , tt) X i) (⟦ Cs ⟧ˢ p X i)

  fmapᶜ : {T : Tel ⟦ P ⟧ᵗ⁰ ℓⁱ} (C : ConD P I T) (e : Σ ⟦ P ⟧ᵗ⁰ ⟦ T ⟧ᵗ)
          (X Y : ⟦ I ⟧ᵗ (fst e) → Set ℓⁱ) → ({i : ⟦ I ⟧ᵗ (fst e)} → X i → Y i)
        → {i : ⟦ I ⟧ᵗ (fst e)} → ⟦ C ⟧ᶜ e X i → ⟦ C ⟧ᶜ e Y i
  fmapᶜ (ι   i  ) e       X Y f eq       = eq
  fmapᶜ (ρ U i C) e       X Y f (x , xs) = (λ u → f (x u)) , fmapᶜ C e X Y f xs
  fmapᶜ (σ A   C) (p , t) X Y f (a , xs) = a , fmapᶜ C (p , (t , a)) X Y f xs

  fmapˢ : (D : SetD P I) (p : ⟦ P ⟧ᵗ⁰) (X Y : ⟦ I ⟧ᵗ p → Set ℓⁱ)
        → ({i : ⟦ I ⟧ᵗ p} → X i → Y i)
        → {i : ⟦ I ⟧ᵗ p} → ⟦ D ⟧ˢ p X i → ⟦ D ⟧ˢ p Y i
  fmapˢ (cons C Cs) p X Y f (inl xs) = inl (fmapᶜ C (p , tt) X Y f xs)
  fmapˢ (cons C Cs) p X Y f (inr xs) = inr (fmapˢ Cs p X Y f xs)

module _ {ℓᵖ ℓⁱ} {P : Tel₀ ℓᵖ} {I : Tel ⟦ P ⟧ᵗ⁰ ℓⁱ}
         (p q : ⟦ P ⟧ᵗ⁰) (it : ⟦ I ⟧ᵗ p → ⟦ I ⟧ᵗ q)
          where

  ParamTransᶜ : {T : Tel ⟦ P ⟧ᵗ⁰ ℓⁱ} → ConD P I T → ⟦ T ⟧ᵗ p → ⟦ T ⟧ᵗ q → Set ℓⁱ
  ParamTransᶜ (ι   i  ) t u = i (q , u) ≡ it (i (p , t))
  ParamTransᶜ (ρ U i C) t u = Σ (Σ (⟦ U ⟧ᵗ (q , u) → ⟦ U ⟧ᵗ (p , t))
                                   λ g → (v : ⟦ U ⟧ᵗ (q , u))
                                       → it (i ((p , t) , g v)) ≡ i ((q , u) , v))
                                λ _ → ParamTransᶜ C t u
  ParamTransᶜ (σ A   C) t u = Σ ((A (p , t) → A (q , u)))
                                λ g → ((a : A (p , t)) → ParamTransᶜ C (t , a) (u , g a))

  ParamTransˢ : SetD P I → Set ℓⁱ
  ParamTransˢ nil         = Unit
  ParamTransˢ (cons C Cs) = Σ (ParamTransᶜ C tt tt) λ _ → ParamTransˢ Cs

  module _ (X : ⟦ I ⟧ᵗ p → Set ℓⁱ) (Y : ⟦ I ⟧ᵗ q → Set ℓⁱ)
           (f : {i : ⟦ I ⟧ᵗ p} → X i → Y (it i)) where

    gmapᶜ : {T : Tel ⟦ P ⟧ᵗ⁰ ℓⁱ} (C : ConD P I T)
            (t : ⟦ T ⟧ᵗ p) (u : ⟦ T ⟧ᵗ q) → ParamTransᶜ C t u
          → {i : ⟦ I ⟧ᵗ p} → ⟦ C ⟧ᶜ (p , t) X i → ⟦ C ⟧ᶜ (q , u) Y (it i)
    gmapᶜ (ι   i  ) t u eq               refl     = eq
    gmapᶜ (ρ U i C) t u ((g , eq) , pts) (x , xs) = (λ v → subst Y (eq v) (f (x (g v))))
                                                  , gmapᶜ C t u pts xs
    gmapᶜ (σ A   C) t u (g  , pts)       (a , xs) = g a
                                                  , gmapᶜ C (t , a) (u , g a) (pts a) xs

    gmapˢ : (E : SetD P I) → ParamTransˢ E
          → {i : ⟦ I ⟧ᵗ p} → ⟦ E ⟧ˢ p X i → ⟦ E ⟧ˢ q Y (it i)
    gmapˢ (cons C Cs) (pt , pts) (inl xs) = inl (gmapᶜ C tt tt pt xs)
    gmapˢ (cons C Cs) (pt , pts) (inr xs) = inr (gmapˢ Cs pts xs)

  gmap : (D : SetD P I) → ParamTransˢ D
       → (Nq : ⟦ I ⟧ᵗ q → Set ℓⁱ) (toNq : {i : ⟦ I ⟧ᵗ q} → ⟦ D ⟧ˢ q Nq i → Nq i)
       → {i : ⟦ I ⟧ᵗ p} → ⟦ D ⟧ˢ p (λ j → Nq (it j)) i → Nq (it i)
  gmap D pt Nq toNq xs = toNq (gmapˢ (λ j → Nq (it j)) Nq (λ n → n) D pt xs)

open import Data.Nat

_ : SetD (snoc (snoc (snoc nil (λ _ → ℕ)) (λ _ → ℕ)) (λ { (tt , fst₁ , n) → {!!}} )) (snoc nil λ { (((x , set) , Level.lift n) , tt) → {!!}})
_ = {!!}

VecD : SetD (snoc nil (λ _ → Set)) (snoc nil (λ _ → ℕ))
VecD = cons (ι (λ _ → tt , 0))
      (cons (σ (λ { ((_ , A) , _) → A })
            (σ (λ _ → ℕ)
            (ρ nil (λ { ((_ , _ , n) , _) → tt , n })
            (ι (λ { (_ , _ , n) → tt , suc n })))))
       nil)

open import Data.Vec

toVec : {p : ⟦ snoc nil (λ _ → Set) ⟧ᵗ⁰} {i : ⟦ snoc nil (λ _ → ℕ) ⟧ᵗ p}
      → ⟦ VecD ⟧ˢ p (λ j → Vec (snd p) (snd j)) i → Vec (snd p) (snd i)
toVec (inl refl)                      = []
toVec (inr (inl (x , _ , xs , refl))) = x ∷ xs tt

fromVec : {p : ⟦ snoc nil (λ _ → Set) ⟧ᵗ⁰} {i : ⟦ snoc nil (λ _ → ℕ) ⟧ᵗ p}
        → Vec (snd p) (snd i) → ⟦ VecD ⟧ˢ p (λ j → Vec (snd p) (snd j)) i
fromVec []       = inl refl
fromVec (x ∷ xs) = inr (inl (x , _ , (λ _ → xs) , refl))

VecParamTrans : (A B : Set) → (A → B) → ParamTransˢ (tt , A) (tt , B) (λ n → n) VecD
VecParamTrans A B f =
  refl , (f , λ a → (λ n → n) , λ n → ((λ _ → tt) , (λ _ → refl)) , refl) , tt

vmap-aux : {A B : Set} → (A → B)
         → ({n : ℕ} → Vec A n → Vec B n) → ({n : ℕ} → Vec A n → Vec B n)
vmap-aux {A} {B} f rec xs =
  gmap (tt , A) (tt , B) (λ n → n) VecD (VecParamTrans A B f) (λ e → Vec B (snd e)) toVec
       (fmapˢ VecD (tt , A) (λ e → Vec A (snd e)) (λ e → Vec B (snd e)) rec (fromVec xs))

--vmap : {A B : Set} → (A → B) → {n : ℕ} → Vec A n → Vec B n
--vmap f []       = {! vmap-aux f (vmap f) [] !}
--vmap f (x ∷ xs) = {! vmap-aux f (vmap f) (x ∷ xs) !}
