{-# OPTIONS -v meta:5 #-}
open import Function
open import Function.Base using (case_of_)
open import Data.Nat
open import Data.Nat.Show
open import Data.Bool using (if_then_else_; true; false)
open import Data.String using (String) renaming (_++_ to _<>_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; zip) renaming (map to map²)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; maybe′; just; nothing; fromMaybe)
open import Data.List using (List; []; _∷_; _++_; map; length; break; [_])
open import Category.Monad
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary --using (Dec; does)
open import Relation.Nullary.Decidable using (True)
open import Reflection
--open import Reflection.Traversal ? ?
open import Agda.Builtin.Reflection
open import PolyUniverse

import Reflection.Name as Name
import Reflection.Argument as A
open import Reflection.Term as Term
import Reflection.Traversal {id} (record { pure = id ; _⊛_ = id }) as T
open import Reflection.DeBruijn

toTelescope : Term → Telescope
toTelescope (pi (arg i x) (abs s y)) = (s , arg i x) ∷ toTelescope y
toTelescope t = [ "_" , vArg t ]

varArgs : {X : Set} → Mono → ℕ → (Mono → ℕ → X) → List (Arg X)
varArgs ∅        n f = []
varArgs I        n f = [ vArg (f I n) ]
varArgs Κ@(K _)  n f = [ vArg (f Κ n) ]
varArgs (M ⊗ M') n f = let ms = varArgs M' n f
                        in varArgs M (n + length ms) f ++ ms


--{-# TERMINATING #-}
--mutual
--  shiftArgs : ℕ → List (Arg Term) → List (Arg Term)
--  shiftArgs n args = map (argMap (shift n)) args
--
--  shift : ℕ → Term → Term
--  shift n (var x args) = var (x + n) (shiftArgs n args)
--  shift n (pi (arg i x) (abs s y)) = pi (arg i (shift n x)) (abs s (shift n y))
--  shift n (con c args) = con c (shiftArgs n args)
--  shift n (def f args) = def f (shiftArgs n args)
--  shift n (lam v (abs s x)) = lam v (abs s (shift n x))
--  shift n t = t

-- number of arguments of a corresponding constructor of a Mono
conArgs : Mono → ℕ
conArgs ∅ = 0
conArgs I = 1
conArgs (K _) = 1
conArgs (M ⊗ M') = conArgs M + conArgs M'

toTyp : Mono → Type → Type → TC Type
toTyp ∅        s t = return t
toTyp I        s t = return (pi (vArg s) (abs "_" (weaken 1 t)))
toTyp (K A)    s t = do a ← quoteTC A --?
                        return (pi (vArg a) (abs "_" (weaken 1 t)))
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

--------
---- specialized generalisation of fold

foldrN : {X : Set} → Alg (ListF ℕ) X (ListN → X)
foldrN e f nil         = e
foldrN e f (cons n ns) = f n (foldrN e f ns)

genFold : Poly → Set → TC Term
genFold F T = quoteTC ({X : Set} → Alg F X (T → X))

replaceμ : Name → Term → Term
replaceμ ν = T.traverseTerm
               (record T.defaultActions
                  {onDef = λ _ name → if does (name Name.≟ quote μ)
                                        then ν
                                        else name})
               (zero T., [])

module _ (ν : Name) (F : Poly) (ϕ : Name) where

  genType : Name → TC Type
  genType f = do typ ← getType f
                 let typ' = replaceμ ϕ typ
                 pT  ← quoteTC F
                 pos ← freshName "_"
                 declarePostulate (vArg pos) typ'
                 t  ← inferType (def pos [ vArg pT ])
                 t' ← normalise t
                 term ← normalise (def f [ vArg pT ])
                 debugPrint "meta" 5 [ termErr t' ]
                 return term


  breakAt : Type → Telescope → Telescope × Telescope
  breakAt target tel = break eq tel
    where eq : (x : String × Arg Type) → Dec (A.unArg (proj₂ x) ≡ target)
          eq (_ , (arg _ x)) = x Term.≟ target

  genClauses : Telescope → String × Arg Type → Telescope
             → Poly → List Name → TC Clauses
  genClauses _ _ _ _ [] = return []
  genClauses _ _ _ [] _ = return []
  genClauses tel₁ x tel₂ (M ∷ G) (n ∷ ns) = do
    cls   ← genClauses tel₁ x tel₂ G ns
    typsᴹ ← varTyps M
    qF    ← quoteTC F
    let len₁ = length tel₁
        lenᴹ = length typsᴹ
        len₂ = length tel₂
        lenTotal = len₁ + lenᴹ + len₂
    term  ← normalise $ def {!!} $
               vArg qF ∷ weakenArgs (lenᴹ + len₂) (vars len₁)
            ++ [ conTerm n ]
            ++ vars len₂
    return $ clause (tel₁
                      ++ map (_,_ "_" ∘ vArg) typsᴹ
                      ++ map (weakenTelescope len₂ lenᴹ) tel₂)
                    (weakenArgPatterns (lenᴹ + len₂) (pats len₁)
                       ++ [ conPat n ]
                       ++ (pats len₂))
                    term
           ∷ cls
    where
      varTyps : Mono → TC (List Type)
      varTyps ∅        = return []
      varTyps I        = return [ def ν [] ]
      varTyps (K A)    = do a ← quoteTC A
                            return [ a ]
      varTyps (M ⊗ M') = do ts  ← varTyps M
                            ts' ← varTyps M'
                            return (ts ++ ts')

      fN : {A : Set} → (ℕ → A) → ℕ → List A
      fN f zero    = []
      fN f (suc n) = f n ∷ fN f n

      pats : ℕ → List (Arg Pattern)
      pats = fN (vArg ∘ var)

      vars : ℕ → List (Arg Term)
      vars = fN λ x → vArg (var x [])

      varPats : List (Arg Pattern)
      varPats = varArgs M 0 λ _ → var

      varTerms : List (Arg Term)
      varTerms = varArgs M 0 λ _ n → var n []

      conPat : Name → Arg Pattern
      conPat ν = vArg (con ν varPats)

      conTerm : Name → Arg Term
      conTerm ν = vArg (con ν varTerms)

      weakenArgPatterns = A.map-Args ∘ weakenFrom′ T.traversePattern 0
      weakenTelescope   = λ a b → map² id (A.map (weakenFrom a b))

  -- Only one occurence of the datatype is supported for now.
  genDef : Type → TC _
  genDef T = do let tel  = toTelescope T
                    tel₁ , tel₂ = breakAt (def ν []) tel
                case tel₂ of λ where
                  [] → typeError [ strErr "no datatype found in the definition." ]
                  ((s , arg _ x) ∷ _) → {!!}
                return tt

--unquoteDecl = genType (quote fold) (ListF ℕ)

--genPat : Name → Poly → TC Term
--genPat n T = {!!}

toVarType : Mono → TC Type
toVarType M = toTyp M (var 0 []) (var 0 [])

toTel : Poly → TC (List Type)
toTel []      = return []
toTel (M ∷ F) = do m  ← toVarType M
                   ms ← toTel F
                   return (m ∷ map (weaken 1) ms)


--cls : Name → TC Clause
--cls ν = do tel ← toTel (ListF ℕ)
--           --let tel = var 0 [] ∷ pi (vArg (quoteTerm ℕ)) (abs "_" (pi (vArg (var 2 [])) (abs "_" (var 3 [])))) ∷ []
--           --debugPrint "meta" 5 (map (strErr ∘ showVar) tel)--(strErr (show (length tel)) ∷ [])
--           return $ clause (("X" , (hArg (quoteTerm Set))) ∷ map (_,_ "_" ∘ vArg)
--                                                                 ( tel ++
--                                                                   quoteTerm ℕ
--                                                                 ∷ quoteTerm ListN
--                                                                 ∷ []))
--                           (hArg (var 4) ∷ map vArg (var 3 ∷ var 2 ∷ con (quote cons) (map vArg (var 1 ∷ var 0 ∷ [])) ∷ []))
--                           (var 2 (map vArg (var 1 [] ∷ def ν (map vArg (var 3 [] ∷ var 2 [] ∷ var 0 [] ∷ [])) ∷ [])))

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


-- assuming given datatype and constructors are generated from F
genFoldDef : Poly → Poly → Name → Name → List Name → TC (List Clause)
genFoldDef _ [] ν funName _              = return []
genFoldDef _ M  ν funName []             = typeError (strErr "number of constructors doesn't match polynomial" ∷ [])
genFoldDef F (M ∷ F') ν funName (ξ ∷ ξs) = do
  cls   ← genFoldDef F F' ν funName ξs
  typs  ← toTel F
  typsᴹ ← varTyps M
  let lenTotal = length typs + length typsᴹ
      varN     = case lenTotal of λ { zero    → zero
                                    ; (suc n) → n }
  --debugPrint "meta" 5 (map termErr typs ++ strErr " " ∷ map termErr typsᴹ)
  --debugPrint "meta" 5 ( strErr (show lenTotal)
  --                    ∷ strErr " "
  --                    ∷ strErr (show (length (foldPats F)))
  --                    ∷ strErr " "
  --                    ∷ strErr (show (length (varPats M)))
  --                    ∷ strErr " "
  --                    ∷ strErr (show (length varTerms))
  --                    ∷ [])
  return (clause (("X" , (hArg (quoteTerm Set)))
                  ∷ map (_,_ "_" ∘ vArg) (typs ++ typsᴹ))
                 (hArg (var lenTotal)
                  ∷ A.map-Args (weakenPattern (length (varPats M))) (foldPats F)
                  ++ [ conPat ξ ])
                 (var (length F' + length typsᴹ) varTerms)
                   ∷ cls)
  where
    varTyps : Mono → TC (List Type)
    varTyps ∅        = return []
    varTyps I        = return [ def ν [] ]
    varTyps (K A)    = do a ← quoteTC A
                          return [ a ]
    varTyps (M ⊗ M') = do ts  ← varTyps M
                          ts' ← varTyps M'
                          return (ts ++ ts')

    foldPats : Poly → List (Arg Pattern)
    foldPats []      = []
    foldPats (_ ∷ F') = vArg (var (length F')) ∷ foldPats F'

    varPats : Mono → List (Arg Pattern)
    varPats M = varArgs M 0 λ _ → var

    conPat : Name → Arg Pattern
    conPat ν = vArg (con ν (varPats M))

    varTerms : List (Arg Term)
    varTerms = varArgs M 0 λ _ n → var n []

    weakenPattern = weakenFrom′ T.traversePattern 0

    --prf : (M : Mono) → conArgs M ≡ length (varPats M)

    --prf I = refl
    --prf (K x) = refl
    --prf (M ⊗ M') = {!!}

--showVar : Term → String
--showVar (var x args) = "Var " <> (show x)
--showVar (pi (arg i t1) (abs s t2)) = "Pi " <> showVar t1 <> " → " <> showVar t2
--showVar T = " others"

testAlg : Poly → Name → TC _
testAlg F foldName = withNormalisation true
                       do a   ← genFold F ListN
                          --cls ← cls foldName
                          cls ← genFoldDef F F (quote ListN) foldName (quote nil ∷ quote cons ∷ [])
                          debugPrint "meta" 5 (termErr a ∷ [])
                          declareDef (vArg foldName) a
                          defineFun foldName (cls)

--unquoteDecl foldN = testAlg (ListF ℕ) foldN

--foldN : {X : Set} → Alg (ListF ℕ) X (ListN → X)
--foldN f g nil = f
--foldN f g (cons x xs) = g x (foldN f {!!} {!!})
