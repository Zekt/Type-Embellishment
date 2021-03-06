{-# OPTIONS --without-K --safe #-}
module Prelude.Function where

open import Agda.Primitive

private variable
  a b c : Level
  A B   : Set a

infixr 9 _∘_ -- _∘₂_
--infixl 8 _ˢ_
--infixl 0 _|>_
infix  0 case_of_ case_return_of_
infixr -100 _$_

id : A → A
id x = x

const : A → (B → A)
const a = λ _ → a

constω : {A : Setω} {B : Set b} → A → (B → A)
constω a = λ _ → a

infix -10 idFun
idFun : (A : Set a) → A → A
idFun A x = x

-- syntax idFun A x = x of A
syntax idFun A x = x ⦂ A

infix -10 idFunω
idFunω : (A : Setω) → A → A
idFunω A x = x

syntax idFunω A x = x ⦂ω A

flip : ∀ {A : Set a} {B : Set b} {C : A → B → Set c} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y
{-# INLINE flip #-}

_∘_ : {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)
{-# INLINE _∘_ #-}

_$_ : {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x
{-# INLINE _$_ #-}

_$ₕ_ : {B : A → Set b} →
      ({x : A} → B x) → ((x : A) → B x)
f $ₕ x = f {x}
{-# INLINE _$_ #-}

_$ᵢ_ : {B : A → Set b} →
      (⦃ x : A ⦄ → B x) → ((x : A) → B x)
f $ᵢ x = f ⦃ x ⦄
{-# INLINE _$_ #-}

case_return_of_ : ∀ {A : Set a} (x : A) (B : A → Set b) →
                  ((x : A) → B x) → B x
case x return B of f = f x
{-# INLINE case_return_of_ #-}

case_of_ : {B : Set b}
  → A → (A → B) → B
case x of f = case x return _ of f
{-# INLINE case_of_ #-}

-- Conversely it is sometimes useful to be able to extract the
-- type of a given expression.

typeOf : {A : Set a} → A → Set a
typeOf {A = A} _ = A

it : ∀ {ℓ} {A : Set ℓ} → ⦃ A ⦄ → A
it ⦃ a ⦄ = a

itω : {A : Setω} → ⦃ A ⦄ → A
itω ⦃ a ⦄ = a
