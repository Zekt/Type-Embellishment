{-# OPTIONS -v meta:5 #-}
open import Function
open import Function.Base using (case_of_)
open import Data.Nat
open import Data.Nat.Show
open import Data.Bool
open import Data.Product using (_×_; _,_; proj₁; proj₂; zip)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty
open import Data.Unit
open import Data.Maybe using (Maybe; maybe′; just; nothing; fromMaybe)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Category.Monad
open import Relation.Binary.PropositionalEquality
open import Reflection
open import Agda.Builtin.Reflection

--------
-- A universe of sums of products

data Mono : Set₁ where
  ∅   : Mono -- alternative form of K ⊤
  I   : Mono
  K   : Set  → Mono
  _⊗_ : Mono → Mono → Mono

Poly : Set₁
Poly = List Mono

⟦_⟧ᴹ : Mono → Set → Set
⟦ ∅      ⟧ᴹ X = ⊤
⟦ I      ⟧ᴹ X = X
⟦ K A    ⟧ᴹ X = A
⟦ M ⊗ M' ⟧ᴹ X = ⟦ M ⟧ᴹ X × ⟦ M' ⟧ᴹ X

⟦_⟧ : Poly → Set → Set
⟦ []    ⟧ X = ⊥
⟦ M ∷ F ⟧ X = ⟦ M ⟧ᴹ X ⊎ ⟦ F ⟧ X

record Def : Set₁ where
  field
    fname : Name
    cons  : List Name
    base  : Poly
    prf   : length cons ≡ length base

fmapᴹ : (M : Mono) {X Y : Set} → (X → Y) → ⟦ M ⟧ᴹ X → ⟦ M ⟧ᴹ Y
fmapᴹ ∅        f _          = tt
fmapᴹ I        f x          = f x
fmapᴹ (K A)    f a          = a
fmapᴹ (M ⊗ M') f (xs , xs') = fmapᴹ M f xs , fmapᴹ M' f xs'

fmap : (F : Poly) {X Y : Set} → (X → Y) → ⟦ F ⟧ X → ⟦ F ⟧ Y
fmap (M ∷ F) f (inj₁ xs) = inj₁ (fmapᴹ M f xs)
fmap (M ∷ F) f (inj₂ xs) = inj₂ (fmap F f xs)

data μ (F : Poly) : Set where
  con : ⟦ F ⟧ (μ F) → μ F

argMap : {X : Set} → (X → X) → Arg X → Arg X
argMap f (arg i x) = arg i (f x)

{-# TERMINATING #-}
shiftVar : ℕ → Term → Term
shiftVar n (var x args) = var (x + n) (map (argMap (shiftVar n)) args)
shiftVar n t = t

-- number of arguments of a constructor of a Mono
conArgs : Mono → ℕ
conArgs ∅ = 0
conArgs I = 1
conArgs (K _) = 1
conArgs (M ⊗ M') = conArgs M + conArgs M'

toTyp : Mono → Name → Type → Type → ℕ → TC Type
toTyp ∅        _ s t n = return (shiftVar n t)
toTyp I        ν s t n = return (pi (vArg (shiftVar n s)) (abs "_" (shiftVar (suc n) t)))
toTyp (K A)    ν s t n = do a ← quoteTC A --?
                            return (pi (vArg a) (abs "_" (shiftVar (suc n) t)))
toTyp (M ⊗ M') ν s t n = do t' ← toTyp M' ν s t (conArgs M)
                            toTyp M ν s t' n

toCon : Mono → Name → TC Type
toCon M ν = toTyp M ν (def ν []) (def ν []) 0

toCons : Poly → Name → TC (List Type)
toCons [] _ = return []
toCons (M ∷ F) ν = do t  ← toCon M ν
                      ts ← toCons F ν
                      return (t ∷ ts)

-- zip that drops tails
zip' : {A B : Set} → List A → List B → List (A × B)
zip' [] _ = []
zip' _ [] = []
zip' (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip' xs ys

genData : Name → List Name → Poly → TC _
genData ν ξs F = do ts ← toCons F ν
                    declareData ν 0 (def (quote Set) [])
                    defineData ν (zip' ξs ts)

-- Specialising to lists
ListF : Set → Poly
ListF A = ∅ ∷ (K A ⊗ I) ∷ []

-- use case
--data ℕ : Set where
--  zero : ℕ
--  suc  : ℕ → ℕ

--_+_ : ℕ → ℕ → ℕ
--zero + b = b
--suc a + b = suc (a + b)

data Dep : ℕ → Set where
  nilV  : Dep zero
  consV : {n : ℕ} → (m : ℕ) → Dep n → Dep (n + m)

unquoteDecl data ListN constructor nil cons =
  genData ListN (nil ∷ cons ∷ []) (ListF ℕ)

toList : {A : Set} → μ (ListF A) → List A
toList (con (inj₁ tt))              = []
toList (con (inj₂ (inj₁ (a , as)))) = a ∷ toList as

fromList : {A : Set} → List A → μ (ListF A)
fromList []       = con (inj₁ tt)
fromList (a ∷ as) = con (inj₂ (inj₁ (a , fromList as)))

conList : {A : Set} → ⟦ ListF A ⟧ (List A) → List A
conList {A} = toList ∘ con ∘ fmap (ListF A) fromList
  -- transporting con by univalence?

conList' : {A : Set} → ⊤ ⊎ A × List A ⊎ ⊥ → List A
conList' (inj₁ tt)              =  conList (inj₁ tt)
conList' (inj₂ (inj₁ (a , as))) =  conList (inj₂ (inj₁ (a , as)))
  -- make toList ∘ fromList = id definitionally (in effect)?
  --   check Allais et al's 'New equations for neutral terms' (DTP 2013)
  -- making toList and fromList meet may be problematic (e.g., when involving if_then_else_)

--------
-- Iteration (fold)

module _ (F : Poly) {X : Set} (f : ⟦ F ⟧ X → X) where

  mutual

    iteration : μ F → X
    iteration (con ds) = f (mapIter F ds)

    mapIter : (G : Poly) (ds : ⟦ G ⟧ (μ F)) → ⟦ G ⟧ X
    mapIter (M ∷ F) (inj₁ ds) = inj₁ (mapIterᴹ M ds)
    mapIter (M ∷ F) (inj₂ ds) = inj₂ (mapIter F ds)

    mapIterᴹ : (M : Mono) (ds : ⟦ M ⟧ᴹ (μ F)) → ⟦ M ⟧ᴹ X
    mapIterᴹ ∅        _          = tt
    mapIterᴹ I        d          = iteration d
    mapIterᴹ (K A   ) a          = a
    mapIterᴹ (M ⊗ M') (ds , ds') = mapIterᴹ M ds , mapIterᴹ M' ds'

-- Specialising to lists

iterList : {A X : Set} → (⟦ ListF A ⟧ X → X) → List A → X
iterList {A} alg as = iteration (ListF A) alg (fromList as)

iterList' : {A X : Set} → (⟦ ListF A ⟧ X → X) → List A → X
iterList' {A} alg []       = iteration (ListF A) alg (fromList [])
iterList' {A} alg (a ∷ as) = iteration (ListF A) alg (fromList (a ∷ as))
  -- have to deal with recursion

-- Curried fold
Algᴹ : (M : Mono) → Set → Set → Set
Algᴹ ∅        X Y = Y
Algᴹ I        X Y = X → Y
Algᴹ (K A   ) X Y = A → Y
Algᴹ (M ⊗ M') X Y = Algᴹ M X (Algᴹ M' X Y)

Alg : (F : Poly) → Set → Set → Set
Alg []      X Y = Y
Alg (M ∷ F) X Y = Algᴹ M X X → Alg F X Y
  -- Y is supposed to be 'the end' of Alg

fromAlgᴹ : (M : Mono) {X Y : Set} → Algᴹ M X Y → ⟦ M ⟧ᴹ X → Y
fromAlgᴹ ∅        alg _ = alg
fromAlgᴹ I        alg = alg
fromAlgᴹ (K A   ) alg = alg
fromAlgᴹ (M ⊗ M') alg (xs , xs') = fromAlgᴹ M' (fromAlgᴹ M alg xs) xs'

toAlg : (F : Poly) {X Y : Set} → ((⟦ F ⟧ X → X) → Y) → Alg F X Y
toAlg []      f = f λ ()
toAlg (M ∷ F) f alg = toAlg F λ g → f λ { (inj₁ xs) → fromAlgᴹ M alg xs
                                        ; (inj₂ xs) → g xs }

fold : (F : Poly) → {X : Set} → Alg F X (μ F → X)
fold F = toAlg F (iteration F)

foldr : {A X : Set} → Alg (ListF A) X (List A → X)
foldr {A} e f as = fold (ListF A) e f (fromList as)

foldr' : {A X : Set} → X → (A → X → X) → List A → X
foldr' {A} e f []       = fold (ListF A) e f (fromList [])
foldr' {A} e f (a ∷ as) = fold (ListF A) e f (fromList (a ∷ as))
  -- in general derived definitions

genFold : Poly → Set → TC Term
genFold F T = quoteTC ({X : Set} → Alg F X (T → X))

varArgs : {X : Set} → Mono → ℕ → (Mono → ℕ → X) → List (Arg X)
varArgs ∅        n f = []
varArgs I        n f = vArg (f I n) ∷ []
varArgs Κ@(K _)  n f = vArg (f Κ n) ∷ []
varArgs (M ⊗ M') n f = let ms = varArgs M' n f
                        in varArgs M (n + length ms) f ++ ms

--varPats : ℕ → Mono → List (Arg Pattern)
--varPats n ∅ = []
--varPats n I = vArg (var n) ∷ []
--varPats n (K _) = vArg (var n) ∷ []
--varPats n (M ⊗ M') = let ms = varPats n M'
--                      in varPats (n + length ms) M ++ ms

--varTerms : ℕ → Mono → List (Arg Term)
--varTerms n ∅ = []
--varTerms n I = vArg (var n []) ∷ []
--varTerms n (K _) = vArg (var n []) ∷ []
--varTerms n (M ⊗ M') = let ms = varTerms n M'
--                       in varTerms (n + length ms) M ++ ms

--patᴹ : Mono → Name → Arg Pattern
--patᴹ M ν = vArg (con ν (varPats 0 M))

--toVarType : Mono → Name → ℕ → TC Type
--toVarType ∅ ν n = return (var n [])
--toVarType I ν n = return (pi (vArg (var n [])) (abs "_" (var (suc n) [])))
--toVarType (K A) ν n = do a ← quoteTC A
--                         return (pi (vArg a) (abs "_" (var (suc n) [])))
--toVarType (M ⊗ M') ν n = do t' ← toVarType M' ν (n + conArgs M)
--                            return {!!}

toVarType : Mono → Name → ℕ → TC Type
toVarType M ν n = toTyp M ν (var 0 []) (var 0 []) n

toTel : Poly → Name → ℕ → TC (List Type)
toTel [] ν n      = return []
toTel (M ∷ F) ν n = do m  ← toVarType M ν n
                       ms ← toTel F ν (conArgs M)
                       return (m ∷ ms)

-- assuming given datatype and constructors are generated from F
genFoldDef : Poly → Poly → Name → List Name → TC (List Clause)
genFoldDef _ [] ν _              = return []
genFoldDef _ M  ν []             = typeError (strErr "number of constructors doesn't match polynomial" ∷ [])
genFoldDef F (M ∷ F') ν (ξ ∷ ξs) = do
  cls   ← genFoldDef F F' ν ξs
  typs  ← toCons F ν
  typsᴹ ← varTyps M
  let lenTotal = length F' + length typsᴹ
      varN     = case lenTotal of λ { zero    → zero
                                    ; (suc n) → n }
  debugPrint "meta" 5 (map termErr (typs ++ typsᴹ))
  debugPrint "meta" 5 ( strErr (show lenTotal)
                      ∷ strErr (show (length varTerms))
                      ∷ [])
  return (clause (map (_,_ "_" ∘ vArg) (typs ++ typsᴹ))
                 (foldPats F ++ (conPat ∷ []))
                 (var lenTotal varTerms)
            ∷ []) -- only one clause for debugging
  where
    varTyps : Mono → TC (List Type)
    varTyps ∅        = return []
    varTyps I        = return ((def ν []) ∷ [])
    varTyps (K A)    = do a ← quoteTC A
                          return (a ∷ [])
    varTyps (M ⊗ M') = do ts  ← varTyps M
                          ts' ← varTyps M
                          return (ts ++ ts')

    varPats : Mono → List (Arg Pattern)
    varPats M = varArgs M 0 λ _ → var

    conPat : Arg Pattern
    conPat = vArg (con ν (varPats M))

    varTerms : List (Arg Term)
    varTerms = varArgs M 0 λ _ n → var n []

    foldPats : Poly → List (Arg Pattern)
    foldPats []      = []
    foldPats (_ ∷ F) = vArg (var (length F + conArgs M)) ∷ foldPats F

    --prf : (M : Mono) → conArgs M ≡ length (varPats M)
    --prf ∅ = refl
    --prf I = refl
    --prf (K x) = refl
    --prf (M ⊗ M') = {!!}

cls : Name → Clause
cls ν = clause (("X" , (hArg (quoteTerm Set))) ∷ map (_,_ "_" ∘ vArg)
                                                     ( var 0 []
                                                     ∷ pi (vArg (quoteTerm ℕ))
                                                          (abs "_" (pi (vArg (var 2 []))
                                                                       (abs "_" (var 3 []))))
                                                     ∷ quoteTerm ℕ
                                                     ∷ quoteTerm ListN
                                                     ∷ []))
               (hArg (var 4) ∷ map vArg (var 3 ∷ var 2 ∷ con (quote cons) (map vArg (var 1 ∷ var 0 ∷ [])) ∷ []))
               (var 2 (map vArg (var 1 [] ∷ def ν (map vArg (var 3 [] ∷ var 2 [] ∷ var 0 [] ∷ [])) ∷ [])))

--foldListN : {X : Set} → X → (ℕ → X → X) → ListN → X
--foldListN e f nil = e
--foldListN e f (cons z l) = f z (foldListN e f l)

--macro
--  testM : Term → TC _
--  testM hole = do types ← toCons (ListF ℕ) (quote ListN)
--                  debugPrint "meta" 5 (map termErr types)
--                  unify hole (quoteTerm tt)
--
--printTyps = testM

--testAlg : Poly → Name → TC _
--testAlg F foldName = withNormalisation true
--                       do a   ← genFold F ListN
--                          --cls ← genFoldDef F F (quote ListN) (quote nil ∷ quote cons ∷ [])
--                          --debugPrint "meta" 5 (termErr a ∷ [])
--                          declareDef (vArg foldName) a
--                          defineFun foldName (cls foldName ∷ [])
--
--unquoteDecl foldN = testAlg (ListF ℕ) foldN

--foldN : {X : Set} → Alg (ListF ℕ) X (ListN → X)
--foldN f g nil = f
--foldN f g (cons x xs) = g x (foldN f {!!} {!!})
