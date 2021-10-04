{-# OPTIONS -v meta:5 #-}
open import Function
open import Function.Base using (case_of_)
open import Data.Nat
open import Data.Nat.Show
open import Data.Bool
open import Data.String using (String) renaming (_++_ to _<>_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; zip)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty
open import Data.Unit
open import Data.Maybe using (Maybe; maybe′; just; nothing; fromMaybe)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Category.Monad
open import Relation.Binary.PropositionalEquality
open import Reflection
--open import Reflection.Traversal ? ?
open import Agda.Builtin.Reflection
open import PolyUniverse

argMap : {X : Set} → (X → X) → Arg X → Arg X
argMap f (arg i x) = arg i (f x)

{-# TERMINATING #-}
mutual
  shiftArgs : ℕ → List (Arg Term) → List (Arg Term)
  shiftArgs n args = map (argMap (shift n)) args

  shift : ℕ → Term → Term
  shift n (var x args) = var (x + n) (shiftArgs n args)
  shift n (pi (arg i x) (abs s y)) = pi (arg i (shift n x)) (abs s (shift n y))
  shift n (con c args) = con c (shiftArgs n args)
  shift n (def f args) = def f (shiftArgs n args)
  shift n (lam v (abs s x)) = lam v (abs s (shift n x))
  shift n t = t

-- number of arguments of a constructor of a Mono
conArgs : Mono → ℕ
conArgs ∅ = 0
conArgs I = 1
conArgs (K _) = 1
conArgs (M ⊗ M') = conArgs M + conArgs M'

toTyp : Mono → Type → Type → TC Type
toTyp ∅        s t = return t
toTyp I        s t = return (pi (vArg s) (abs "_" (shift 1 t)))
toTyp (K A)    s t = do a ← quoteTC A --?
                        return (pi (vArg a) (abs "_" (shift 1 t)))
toTyp (M ⊗ M') s t = do t' ← toTyp M' s t
                        toTyp M s t'

toCon : Mono → Name → TC Type
toCon M ν = toTyp M (def ν []) (def ν [])

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

unquoteDecl data ListN constructor nil cons =
  genData ListN (nil ∷ cons ∷ []) (ListF ℕ)

---- specialized generation of fold

foldrN : {X : Set} → Alg (ListF ℕ) X (ListN → X)
foldrN e f nil         = e
foldrN e f (cons n ns) = f n (foldrN e f ns)

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

toVarType : Mono → TC Type
toVarType M = toTyp M (var 0 []) (var 0 [])

toTel : Poly → TC (List Type)
toTel []      = return []
toTel (M ∷ F) = do m  ← toVarType M
                   ms ← toTel F
                   return (m ∷ map (shift 1) ms)

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

    --prf I = refl
    --prf (K x) = refl
    --prf (M ⊗ M') = {!!}

--showVar : Term → String
--showVar (var x args) = "Var " <> (show x)
--showVar (pi (arg i t1) (abs s t2)) = "Pi " <> showVar t1 <> " → " <> showVar t2
--showVar T = " others"

cls : Name → TC Clause
cls ν = do tel ← toTel (ListF ℕ)
           --let tel = var 0 [] ∷ pi (vArg (quoteTerm ℕ)) (abs "_" (pi (vArg (var 2 [])) (abs "_" (var 3 [])))) ∷ []
           --debugPrint "meta" 5 (map (strErr ∘ showVar) tel)--(strErr (show (length tel)) ∷ [])
           return $ clause (("X" , (hArg (quoteTerm Set))) ∷ map (_,_ "_" ∘ vArg)
                                                                 ( tel ++
                                                                   quoteTerm ℕ
                                                                 ∷ quoteTerm ListN
                                                                 ∷ []))
                           (hArg (var 4) ∷ map vArg (var 3 ∷ var 2 ∷ con (quote cons) (map vArg (var 1 ∷ var 0 ∷ [])) ∷ []))
                           (var 2 (map vArg (var 1 [] ∷ def ν (map vArg (var 3 [] ∷ var 2 [] ∷ var 0 [] ∷ [])) ∷ [])))

--∅ ∷ K ℕ ⊗ I ∷ []
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

testAlg : Poly → Name → TC _
testAlg F foldName = withNormalisation true
                       do a   ← genFold F ListN
                          cls ← cls foldName
                          --cls ← genFoldDef F F (quote ListN) (quote nil ∷ quote cons ∷ [])
                          --debugPrint "meta" 5 (termErr a ∷ [])
                          declareDef (vArg foldName) a
                          defineFun foldName (cls ∷ [])

--unquoteDecl foldN = testAlg (ListF ℕ) foldN

--foldN : {X : Set} → Alg (ListF ℕ) X (ListN → X)
--foldN f g nil = f
--foldN f g (cons x xs) = g x (foldN f {!!} {!!})
