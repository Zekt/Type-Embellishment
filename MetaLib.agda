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
open import Data.List using (List; []; _∷_; _++_; map; length; break; [_]; concat)
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
import Reflection.Traversal {id} (record { pure = id ; _⊛_ = id }) as Trav
import Reflection.Traversal {TC} (record { pure = return
                                         ; _⊛_ = λ A→Bᵀ Aᵀ → A→Bᵀ >>= λ A→B
                                                           → bindTC Aᵀ (return ∘ A→B) }) as TravTC
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

--------
---- specialized generalisation of fold

--foldrN : {X : Set} → Alg (ListF ℕ) X (ListN → X)
--foldrN e f nil         = e
--foldrN e f (cons n ns) = f n (foldrN e f ns)

genFold : Poly → Set → TC Term
genFold F T = quoteTC ({X : Set} → Alg F X (T → X))

replaceμ : Name → Term → Term
replaceμ ν = Trav.traverseTerm
               (record Trav.defaultActions
                  {onDef = λ _ name → if does (name Name.≟ quote μ)
                                        then ν
                                        else name})
               (zero Trav., [])

breakAt : Type → Telescope → Telescope × Telescope
breakAt target tel = break eq tel
  where eq : (a : String × Arg Type) → Dec (A.unArg (proj₂ a) ≡ target)
        eq (_ , (arg _ x)) = x Term.≟ target


--import Reflection.Traversal TC ? as TCTerm

weakenArgPatterns = A.map-Args ∘ weakenFrom′ Trav.traversePattern 0
-- Modify the telescope after the occurence of the target datatype.
-- Since the occurence is now replaced with a pattern of a constructor and arguments,
-- the De Brujin index could be weakened, but more importantly, it could
-- be reduced by one (i.e. when the constructor takes no arguments).
shiftTel : ℕ → List (String × Arg Term) → List (String × Arg Term)
shiftTel zero = Trav.traverseTel
                  (record Trav.defaultActions {
                            onVar = λ {
                              (len Trav., _) n → if n <ᵇ len then n else n ∸ 1
                            } -- Might be prone to errors!
                          })
                  (zero Trav., [])
shiftTel (suc n) = weakenFrom′ Trav.traverseTel 0 n
--shiftTel from zero (str , arg _ x) = do x ← TravTC.traverseTerm
--                                              (record TravTC.defaultActions {
--                                                        onVar = λ where
--                                                          Γ zero → typeError [ strErr "De Brujin index of the original type is malformed." ]
--                                                          Γ (suc n) → return n
--                                                      })
--                                              (zero TravTC., [])
--                                              x
--                                        return {!!}
--weakenTel : ℕ → ℕ → (String × Arg Term) → (String × Arg Term)
--weakenTel = λ a b → map² id (A.map (weakenFrom a b))

-- ν is the name of the function to be translated, e.g. fold.
-- F is the polynomial definition of the target datatype that should appears in the type of ν.
-- The target datatype is assumed to be represented by μ : Poly → Set.
-- ϕ is the transformation to be substituted for μ.

module _ (ν : Name) (F : Poly) (ϕ : Name) where

  genMonoTypes : Mono → TC (List Type)
  genMonoTypes ∅        = return []
  genMonoTypes I        = return [ def ν [] ]
  genMonoTypes (K A)    = do a ← quoteTC A
                             return [ a ]
  genMonoTypes (M ⊗ M') = do ts ← genMonoTypes M
                             ts' ← genMonoTypes M'
                             return (ts ++ ts')

  genType : TC Type
  genType = do typ ← getType ν
               let typ' = replaceμ ϕ typ
               qF  ← quoteTC F
               pos ← freshName "_"
               declarePostulate (vArg pos) typ'
               t  ← inferType (def pos [ vArg qF ])
               t' ← normalise t
               μtyp ← inferType (def ν [ vArg qF ])
               μtyp' ← normalise μtyp
               debugPrint "meta" 5 [ termErr μtyp' ]
               return t'

  -- generate the clauses with two list of types that appear in the patterns,
  -- between which the deconstructed target datatype should be in the middle.
  genClauses : Telescope → Telescope
             → Poly → List Name → TC Clauses
  genClauses _ _ _ [] = return []
  genClauses _ _ [] _ = return []
  genClauses tel₁ tel₂ (M ∷ G) (n ∷ ns) = do
    cls   ← genClauses tel₁ tel₂ G ns
    typsᴹ ← genMonoTypes M
    qF    ← quoteTC F
    let len₁ = length tel₁
        lenᴹ = length typsᴹ
        len₂ = length tel₂
        lenTotal = len₁ + lenᴹ + len₂
    term  ← return $ con n (
               vArg qF ∷ weakenArgs (lenᴹ + len₂) (vars len₁)
            ++ [ conTerm n ]
            ++ vars len₂)
    debugPrint "meta" 5 [ strErr (showTerm term) ]
    return $ clause (tel₁
                      ++ map (_,_ "_" ∘ vArg) typsᴹ
                      ++ shiftTel lenᴹ tel₂)
                    (weakenArgPatterns (lenᴹ + len₂) (pats len₁)
                       ++ [ conPat n ]
                       ++ (pats len₂))
                    term
           ∷ cls
    where

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


  -- Only one occurence of the datatype is supported for now.
  -- genFun firstly calls genType,
  --   * it replaces μ with ϕ and normalises the function type.
  -- Then it calls genClauses,
  --   * it starts from the type before replacing μ,
  --   * parses it and splits it at the first occurence of μ.
  genFun : Name → List Name → TC _
  genFun f cs = do funType ← genType
                   declareDef (vArg f) funType
                   qF' ← quoteTC F
                   qF ← normalise qF'
                   T' ← inferType (def ν [ vArg qF ])
                   T ← normalise T'
                   let tel  = toTelescope T
                       tel₁ , xtel₂ = break (≟-μ qF) tel
                   tel₂ ← case xtel₂ of λ where
                     [] → typeError [ strErr "no datatype found in the definition." ]
                     (_ ∷ xs) → return xs
                   debugPrint "meta" 5 [ strErr (showTel tel₂) ]
                   cls ← genClauses tel₁ tel₂ F cs
                   debugPrint "meta" 5 [ strErr (showClauses cls) ]
                   defineFun f cls
                   return tt
    where
    -- The decidable equality should identify something like (μ (∅ ∷ (K ℕ ⊗ I) ∷ []))
      ≟-μ : (qF : Type) → (x : String × Arg Type)
          → Dec (A.unArg (proj₂ x) ≡ def (quote μ) [ vArg qF ])
      ≟-μ qF (_ , arg _ x) = x Term.≟ def (quote μ) [ vArg qF ]


--------
-- Examples, this part should be user-defined.
-- A ϕ transformation from the univserse to native datatype should be defined.
-- For example, A (ListF ℕ) in Poly should be mapped to native (List ℕ).
-- genFun : (ν : Name) (F : Poly) (ϕ : Name) → Name → List Name → TC _

unquoteDecl data ListN constructor nilN consN =
  genData ListN (nilN ∷ consN ∷ []) (ListF ℕ)

ϕ : Poly → Set
ϕ _ = ListN

--unquoteDecl foldN = genFun (quote fold) (ListF ℕ) (quote ϕ) foldN (quote nilN ∷ quote consN ∷ [])

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
--genFoldDef : Poly → Poly → Name → Name → List Name → TC (List Clause)
--genFoldDef _ [] ν funName _              = return []
--genFoldDef _ M  ν funName []             = typeError (strErr "number of constructors doesn't match polynomial" ∷ [])
--genFoldDef F (M ∷ F') ν funName (ξ ∷ ξs) = do
--  cls   ← genFoldDef F F' ν funName ξs
--  typs  ← toTel F
--  typsᴹ ← varTyps M
--  let lenTotal = length typs + length typsᴹ
--      varN     = case lenTotal of λ { zero    → zero
--                                    ; (suc n) → n }
  --debugPrint "meta" 5 (map termErr typs ++ strErr " " ∷ map termErr typsᴹ)
  --debugPrint "meta" 5 ( strErr (show lenTotal)
  --                    ∷ strErr " "
  --                    ∷ strErr (show (length (foldPats F)))
  --                    ∷ strErr " "
  --                    ∷ strErr (show (length (varPats M)))
  --                    ∷ strErr " "
  --                    ∷ strErr (show (length varTerms))
  --                    ∷ [])
  --return (clause (("X" , (hArg (quoteTerm Set)))
  --                ∷ map (_,_ "_" ∘ vArg) (typs ++ typsᴹ))
  --               (hArg (var lenTotal)
  --                ∷ A.map-Args (weakenPattern (length (varPats M))) (foldPats F)
  --                ++ [ conPat ξ ])
  --               (var (length F' + length typsᴹ) varTerms)
  --                 ∷ cls)
  --where
  --  varTyps : Mono → TC (List Type)
  --  varTyps ∅        = return []
  --  varTyps I        = return [ def ν [] ]
  --  varTyps (K A)    = do a ← quoteTC A
  --                        return [ a ]
  --  varTyps (M ⊗ M') = do ts  ← varTyps M
  --                        ts' ← varTyps M'
  --                        return (ts ++ ts')

  --  foldPats : Poly → List (Arg Pattern)
  --  foldPats []      = []
  --  foldPats (_ ∷ F') = vArg (var (length F')) ∷ foldPats F'

  --  varPats : Mono → List (Arg Pattern)
  --  varPats M = varArgs M 0 λ _ → var

  --  conPat : Name → Arg Pattern
  --  conPat ν = vArg (con ν (varPats M))

  --  varTerms : List (Arg Term)
  --  varTerms = varArgs M 0 λ _ n → var n []

  --  weakenPattern = weakenFrom′ T.traversePattern 0

    --prf : (M : Mono) → conArgs M ≡ length (varPats M)

    --prf I = refl
    --prf (K x) = refl
    --prf (M ⊗ M') = {!!}

--showVar : Term → String
--showVar (var x args) = "Var " <> (show x)
--showVar (pi (arg i t1) (abs s t2)) = "Pi " <> showVar t1 <> " → " <> showVar t2
--showVar T = " others"

--testAlg : Poly → Name → TC _
--testAlg F foldName = withNormalisation true
--                       do a   ← genFold F ListN
--                          --cls ← cls foldName
--                          cls ← genFoldDef F F (quote ListN) foldName (quote nil ∷ quote cons ∷ [])
--                          debugPrint "meta" 5 (termErr a ∷ [])
--                          declareDef (vArg foldName) a
--                          defineFun foldName (cls)

--unquoteDecl foldN = testAlg (ListF ℕ) foldN

--foldN : {X : Set} → Alg (ListF ℕ) X (ListN → X)
--foldN f g nil = f
--foldN f g (cons x xs) = g x (foldN f {!!} {!!})
