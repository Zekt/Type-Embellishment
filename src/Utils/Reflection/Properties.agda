{-# OPTIONS --without-K --safe #-}
open import Prelude

module Utils.Reflection.Properties where
open import Agda.Builtin.Reflection as Builtin

private variable
  A B : Set _
  
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
