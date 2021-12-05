{-# OPTIONS --safe #-}
module Utils.Reflection.Core where

open import Prelude

open import Agda.Builtin.Reflection as Builtin
open Builtin public
  hiding ( primQNameEquality
         ; primQNameLess
         ; primShowQName
         ; primMetaEquality
         ; primMetaLess
         ; primShowMeta )

private variable
  A B : Set _

-- Types
  
Clauses   = List Clause
Telescope = List (String × Arg Type)

Args : Set ℓ → Set ℓ
Args A = List (Arg A)

Tactic = Term → TC ⊤

--- Terms ---

pattern `Set₀ = agda-sort (lit 0)
pattern `Set₁ = agda-sort (lit 1)
pattern `Set₂ = agda-sort (lit 2)

pattern `Set! = agda-sort unknown

pattern default-modality = modality relevant quantity-ω

pattern vArg x = arg (arg-info visible default-modality) x
pattern hArg x = arg (arg-info hidden default-modality) x
pattern iArg x = arg (arg-info instance′ default-modality) x

pattern var₀ x         = var x []
pattern var₁ x a       = var x (vArg a ∷ [])
pattern var₂ x a b     = var x (vArg a ∷ vArg b ∷ [])
pattern var₃ x a b c   = var x (vArg a ∷ vArg b ∷ vArg c ∷ [])
pattern var₄ x a b c d = var x (vArg a ∷ vArg b ∷ vArg c ∷ vArg d ∷ [])

pattern con₀ c         = con c []
pattern con₁ c x       = con c (vArg x ∷ [])
pattern con₂ c x y     = con c (vArg x ∷ vArg y ∷ [])
pattern con₃ c x y z   = con c (vArg x ∷ vArg y ∷ vArg z ∷ [])
pattern con₄ c x y z u = con c (vArg x ∷ vArg y ∷ vArg z ∷ vArg u ∷ [])

pattern def₀ f         = def f []
pattern def₁ f x       = def f (vArg x ∷ [])
pattern def₂ f x y     = def f (vArg x ∷ vArg y ∷ [])
pattern def₃ f x y z   = def f (vArg x ∷ vArg y ∷ vArg z ∷ [])
pattern def₄ f x y z u = def f (vArg x ∷ vArg y ∷ vArg z ∷ vArg u ∷ [])

pattern vLam x = lam visible x
pattern hLam x = lam hidden x
pattern iLam x = lam instance′ x

unArg : Arg A → A
unArg (arg _ x) = x

getArgInfo : Arg A → ArgInfo
getArgInfo (arg i _) = i

getVisibility : Arg A → Visibility
getVisibility (arg (arg-info v _) _) = v

getModality : Arg A → Modality
getModality (arg (arg-info _ m) _) = m

getRelevance : Arg A → Relevance
getRelevance (arg (arg-info _ (modality r _)) _) = r

getQuantity : Arg A → Quantity
getQuantity (arg (arg-info _ (modality _ q)) _) = q

isVisible : Arg A → Bool
isVisible (arg (arg-info visible _) _) = true
isVisible _ = false

instance
  FunctorArg : Functor Arg
  fmap {{FunctorArg}} f (arg i x) = arg i (f x)

  ArgsFunctor : Functor λ A → List (Arg A)
  fmap ⦃ ArgsFunctor ⦄ f []       = []
  fmap ⦃ ArgsFunctor ⦄ f (x ∷ xs) = fmap f x ∷ fmap f xs

unAbs : Abs A → A
unAbs (abs _ x) = x

instance
  FunctorAbs : Functor Abs
  fmap {{FunctorAbs}} f (abs s x) = abs s (f x)

absurd-lam : Term
absurd-lam = pat-lam (absurd-clause (("()" , vArg unknown) ∷ []) (vArg (absurd 0) ∷ []) ∷ []) []

--- TC monad ---

mapTC : (A → B) → TC A → TC B
mapTC f m = bindTC m λ x → returnTC (f x)

instance
  FunctorTC : Functor TC
  fmap ⦃ FunctorTC ⦄ = mapTC

  ApplicativeTC : Applicative TC
  pure  ⦃ ApplicativeTC ⦄ = returnTC
  _<*>_ ⦃ ApplicativeTC ⦄ = monadAp bindTC

  MonadTC : Monad TC
  _>>=_  ⦃ MonadTC ⦄ = bindTC

  FunctorZeroTC : FunctorZero TC
  empty ⦃ FunctorZeroTC ⦄ = typeError []

  AlternativeTC : Alternative TC
  _<|>_ ⦃ AlternativeTC ⦄ = catchTC


give : Term → Tactic
give v = λ hole → unify hole v

define : Arg Name → Type → List Clause → TC ⊤
define f a cs = declareDef f a >> defineFun (unArg f) cs

newMeta : Type → TC Term
newMeta = checkType unknown

newMeta! : TC Term
newMeta! = newMeta unknown

typeErrorS : String → TC A
typeErrorS s = typeError (strErr s ∷ [])

blockOnMeta! : Meta → TC A
blockOnMeta! x = commitTC >>= λ _ → blockOnMeta x

inferNormalisedType : Term → TC Type
inferNormalisedType t = withNormalisation true (inferType t)

-- Injectivity of constructors

arg-inj₁ : ∀ {i i′} {x x′ : A} → arg i x ≡ arg i′ x′ → i ≡ i′
arg-inj₁ refl = refl

arg-inj₂ : ∀ {i i′} {x x′ : A} → arg i x ≡ arg i′ x′ → x ≡ x′
arg-inj₂ refl = refl

arg-info-inj₁ : ∀ {v v′ r r′} → arg-info v r ≡ arg-info v′ r′ → v ≡ v′
arg-info-inj₁ refl = refl

arg-info-inj₂ : ∀ {v v′ r r′} → arg-info v r ≡ arg-info v′ r′ → r ≡ r′
arg-info-inj₂ refl = refl

modality-inj₁ : ∀ {r r′ q q′} → modality r q ≡ modality r′ q′ → r ≡ r′
modality-inj₁ refl = refl

modality-inj₂ : ∀ {r r′ q q′} → modality r q ≡ modality r′ q′ → q ≡ q′
modality-inj₂ refl = refl

abs-inj₁ : ∀ {s s′} {x x′ : A} → abs s x ≡ abs s′ x′ → s ≡ s′
abs-inj₁ refl = refl

abs-inj₂ : ∀ {s s′} {x x′ : A} → abs s x ≡ abs s′ x′ → x ≡ x′
abs-inj₂ refl = refl

--- Terms ---

var-inj₁ : ∀ {x x′ args args′} → Term.var x args ≡ var x′ args′ → x ≡ x′
var-inj₁ refl = refl

var-inj₂ : ∀ {x x′ args args′} → Term.var x args ≡ var x′ args′ → args ≡ args′
var-inj₂ refl = refl

con-inj₁ : ∀ {c c′ args args′} → Term.con c args ≡ con c′ args′ → c ≡ c′
con-inj₁ refl = refl

con-inj₂ : ∀ {c c′ args args′} → Term.con c args ≡ con c′ args′ → args ≡ args′
con-inj₂ refl = refl

def-inj₁ : ∀ {f f′ args args′} → def f args ≡ def f′ args′ → f ≡ f′
def-inj₁ refl = refl

def-inj₂ : ∀ {f f′ args args′} → def f args ≡ def f′ args′ → args ≡ args′
def-inj₂ refl = refl

meta-inj₁ : ∀ {f f′ args args′} → Term.meta f args ≡ meta f′ args′ → f ≡ f′
meta-inj₁ refl = refl

meta-inj₂ : ∀ {f f′ args args′} → Term.meta f args ≡ meta f′ args′ → args ≡ args′
meta-inj₂ refl = refl

lam-inj₁ : ∀ {v v′ t t′} → lam v t ≡ lam v′ t′ → v ≡ v′
lam-inj₁ refl = refl

lam-inj₂ : ∀ {v v′ t t′} → lam v t ≡ lam v′ t′ → t ≡ t′
lam-inj₂ refl = refl

pat-lam-inj₁ : ∀ {v v′ t t′} → pat-lam v t ≡ pat-lam v′ t′ → v ≡ v′
pat-lam-inj₁ refl = refl

pat-lam-inj₂ : ∀ {v v′ t t′} → pat-lam v t ≡ pat-lam v′ t′ → t ≡ t′
pat-lam-inj₂ refl = refl

pi-inj₁ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₁ ≡ t₁′
pi-inj₁ refl = refl

pi-inj₂ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₂ ≡ t₂′
pi-inj₂ refl = refl

sort-inj : ∀ {x y} → agda-sort x ≡ agda-sort y → x ≡ y
sort-inj refl = refl

lit-inj : ∀ {x y} → Term.lit x ≡ lit y → x ≡ y
lit-inj refl = refl

--- Sorts ---

set-inj : ∀ {x y} → set x ≡ set y → x ≡ y
set-inj refl = refl

prop-inj : ∀ {x y} → prop x ≡ prop y → x ≡ y
prop-inj refl = refl

slit-inj : ∀ {x y} → Sort.lit x ≡ lit y → x ≡ y
slit-inj refl = refl

spropLit-inj : ∀ {x y} → Sort.propLit x ≡ propLit y → x ≡ y
spropLit-inj refl = refl

sinf-inj : ∀ {x y} → Sort.inf x ≡ inf y → x ≡ y
sinf-inj refl = refl

--- Patterns ---

pcon-inj₁ : ∀ {x y z w} → Pattern.con x y ≡ con z w → x ≡ z
pcon-inj₁ refl = refl

pcon-inj₂ : ∀ {x y z w} → Pattern.con x y ≡ con z w → y ≡ w
pcon-inj₂ refl = refl

pvar-inj : ∀ {x y} → Pattern.var x ≡ var y → x ≡ y
pvar-inj refl = refl

pdot-inj : ∀ {x y} → Pattern.dot x ≡ dot y → x ≡ y
pdot-inj refl = refl

plit-inj : ∀ {x y} → Pattern.lit x ≡ lit y → x ≡ y
plit-inj refl = refl

proj-inj : ∀ {x y} → Pattern.proj x ≡ proj y → x ≡ y
proj-inj refl = refl

absurd-inj : ∀ {x y} → absurd x ≡ absurd y → x ≡ y
absurd-inj refl = refl

--- Clauses ---

clause-inj₁ : ∀ {x y z u v w} → clause x y z ≡ clause u v w → x ≡ u
clause-inj₁ refl = refl

clause-inj₂ : ∀ {x y z u v w} → clause x y z ≡ clause u v w → y ≡ v
clause-inj₂ refl = refl

clause-inj₃ : ∀ {x y z u v w} → clause x y z ≡ clause u v w → z ≡ w
clause-inj₃ refl = refl

absurd-clause-inj₁ : ∀ {x y z w} → absurd-clause x y ≡ absurd-clause z w → x ≡ z
absurd-clause-inj₁ refl = refl

absurd-clause-inj₂ : ∀ {x y z w} → absurd-clause x y ≡ absurd-clause z w → y ≡ w
absurd-clause-inj₂ refl = refl

--- Literals ---

nat-inj : ∀ {x y} → nat x ≡ nat y → x ≡ y
nat-inj refl = refl

word64-inj : ∀ {x y} → word64 x ≡ word64 y → x ≡ y
word64-inj refl = refl

float-inj : ∀ {x y} → float x ≡ float y → x ≡ y
float-inj refl = refl

char-inj : ∀ {x y} → char x ≡ char y → x ≡ y
char-inj refl = refl

string-inj : ∀ {x y} → string x ≡ string y → x ≡ y
string-inj refl = refl

name-inj : ∀ {x y} → name x ≡ name y → x ≡ y
name-inj refl = refl

meta-inj : ∀ {x y} → Literal.meta x ≡ meta y → x ≡ y
meta-inj refl = refl
