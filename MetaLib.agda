{-# OPTIONS -v meta:5 #-}
open import Level using (0ℓ)

open import Function
open import Function.Base using (case_of_)
open import Data.Nat as N
open import Agda.Builtin.Nat using (_==_)
import Data.Nat.GeneralisedArithmetic as G using (fold)
open import Data.Nat.Show
open import Data.Bool using (if_then_else_; true; false)
open import Data.String using (String) renaming (_++_ to _<>_)
open import Data.Product using (Σ; Σ-syntax; ∃; ∃-syntax; _×_; _,_; proj₁; proj₂) renaming (map to map²)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; maybe′; just; nothing; fromMaybe)
open import Data.List using (List; []; _∷_; _++_; map; length; break; [_]; concat; zip; foldr; lookup)
open import Data.Fin using (Fin; fromℕ; fromℕ<; fromℕ<″)
open import Category.Monad
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary --using (Dec; does)
open import Relation.Nullary.Decidable using (True)

open import Reflection
open import Agda.Builtin.Reflection
open import Reflection.TypeChecking.Monad.Syntax
import Reflection.Name as Name
import Reflection.Argument as A
open import Reflection.Term as Term
import Reflection.Traversal {id} (record { pure = id ; _⊛_ = id }) as Trav
import Reflection.Traversal {TC} (record { pure = return
                                         ; _⊛_ = λ A→Bᵀ Aᵀ → A→Bᵀ >>= λ A→B
                                                           → bindTC Aᵀ (return ∘ A→B) }) as TravTC
open import Reflection.DeBruijn

open import PolyUniverse

piToTel : Term → Telescope
piToTel (pi (arg i x) (abs s y)) = (s , arg i x) ∷ piToTel y
piToTel t = [] -- ignoring the last term in a pi chain

fromMonoGenArgs : {X : Set} → Mono → ℕ → (Mono → ℕ → X) → List (Arg X)
fromMonoGenArgs ∅        n f = []
fromMonoGenArgs I        n f = [ vArg (f I n) ]
fromMonoGenArgs Κ@(K _)  n f = [ vArg (f Κ n) ]
fromMonoGenArgs (M ⊗ M') n f = let ms = fromMonoGenArgs M' n f
                                in fromMonoGenArgs M (n + length ms) f ++ ms

⟪_⟫ : Mono → Type → Type → TC Type
⟪_⟫ ∅        s t = return t
⟪_⟫ I        s t = return (pi (vArg s) (abs "_" (weaken 1 t)))
⟪_⟫ (K A)    s t = do a ← quoteTC A --?
                      return (pi (vArg a) (abs "_" (weaken 1 t)))
⟪_⟫ (M ⊗ M') s t = ⟪ M' ⟫ s t >>= ⟪ M ⟫ s

monoType : Mono → TC Type
monoType M = ⟪ M ⟫ (var 0 []) (var 0 [])

polyTel : Poly → TC (List Type)
polyTel []      = return []
polyTel (M ∷ F) = do m  ← monoType M
                     ms ← polyTel F
                     return (m ∷ map (weaken 1) ms)

-- the corresponding constructor type of a Mono
toConDef : Mono → Name → TC Type
toConDef M ν = ⟪ M ⟫ (def ν []) (def ν [])

toConCon : Mono → Name → TC Type
toConCon M ν = ⟪ M ⟫ (con ν []) (con ν [])

toConDefs : Poly → Name → TC (List Type)
toConDefs [] _ = return []
toConDefs (M ∷ F) ν = ⦇ toConDef M ν ∷ toConDefs F ν ⦈

genData : Name → List Name → Poly → TC _
genData ν ξs F = do ts ← toConDefs F ν
                    declareData ν 0 (def (quote Set) [])
                    defineData ν (zip ξs ts)

unquoteDecl data ListN constructor nilN consN =
  genData ListN (nilN ∷ consN ∷ []) (ListF ℕ)

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

weakenArgPats = A.map-Args ∘ weakenFrom′ Trav.traversePattern 0
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

--data _∈_ : Mono → Poly → Set where
--  here  : {M : Mono} → {F : Poly} → M ∈ (M ∷ F)
--  there : {M' : Mono} → {M : Mono} → {F : Poly} → M ∈ F → M ∈ (M' ∷ F)
--
--getTerm : {M : Mono} {F : Poly} → M ∈ F → μ F → TC Term
--getTerm {M} {.(_ ∷ _)} (there M∈F) μF = {!!}

parseCon : Name → Mono → TC Telescope
parseCon n M = do t  ← getType n
                  --debugPrint "meta" 5 (termErr t ∷ [])
                  tᴹ ← inferType (con n [])
                  --debugPrint "meta" 5 (termErr tᴹ ∷ [])
                  let d   = t Term.≟ tᴹ
                      tel = piToTel t
                  if (does d)
                    then return tel
                    else typeError (strErr "Given datatype constructor "
                                   ∷ termErr t
                                   ∷ strErr " and Mono definition "
                                   ∷ termErr tᴹ
                                   ∷ strErr " does not match."
                                   ∷ [])

--prodType : Telescope → Type
--prodType [] = quoteTerm ⊤
--prodType ((_ , arg _ x) ∷ xs) = def (quote _×_)
--                                    (hArg (quoteTerm 0ℓ)
--                                    ∷ hArg (quoteTerm 0ℓ)
--                                    ∷ vArg x
--                                    ∷ vArg (prodType xs)
--                                    ∷ [])

-- fromList : ListN → μ (ListF ℕ)
-- inj₁ _
-- inj₂ (inj₁ _)
-- inj₂ (inj₂ (inj₁ _))
-- ...
genFromClauses : Name → Type → List Name → Poly → Poly → TC Clauses
genFromClauses _ _ [] [] _ = return []
genFromClauses funName typ (n ∷ ns) (M ∷ Ms) F = do
  tel ← parseCon n M
  let len = length tel
      term = prodTerm (recurse tel typ) len
      cl = clause
             tel
             [ vArg $ con n (pats tel) ]
           $ con (quote μ.con)
                 [ vArg $ inj (length F ∸ length Ms) term ]
  --debugPrint "meta" 5 [ strErr (showClause cl) ]
  cls ← genFromClauses funName typ ns Ms F
  return (cl ∷ cls)
  where
    pats : Telescope → List (Arg Pattern)
    pats = foldr (λ { (_ , arg i _) xs → arg i (var (length xs)) ∷ xs}) []

    -- lookup from last
    lookupCxt : ∀ {A : Set} → List A → ℕ → Maybe A
    lookupCxt xs n with n <? length xs
    ... | no  _ = nothing
    ... | yes p = just $ lookup xs (fromℕ< (reverse< p))
      where
        <≤ : ∀ {a b} → a < b → a ≤ b
        <≤ (s≤s z≤n) = z≤n
        <≤ (s≤s (s≤s a<b)) = s≤s (<≤ (s≤s a<b))

        reverse< : ∀ {a b : ℕ} → (a < b) → (b ∸ (a + 1)) < b
        reverse< {zero} {suc zero} a<b = s≤s z≤n
        reverse< {zero} {suc (suc b)} a<b = s≤s (reverse< (s≤s z≤n))
        reverse< {suc a} {suc (suc b)} (s≤s a<b) = s≤s (<≤ (reverse< a<b))


    recurse : Telescope → Type → Term → Term
    recurse tel target t@(var x args) =
      case lookupCxt tel x of λ where
        (just (_ , arg _ typ)) → if does (typ Term.≟ target) then
                                   def funName [ vArg t ]
                                 else t
        nothing → t
    recurse tel _ t = t

    prodTerm : (Term → Term) → ℕ → Term
    prodTerm f = proj₂ ∘
                 G.fold (0 , quoteTerm tt)
                        λ { (zero  , t) →
                               suc zero , f (var 0 [])
                          ; (suc n , t) →
                               suc (suc n)
                             , con (quote _,_)
                                   (vArg (f (var (suc n) []))
                                   ∷ [ vArg t ])
                          }

    inj : ℕ → Term → Term
    inj zero t = t
    inj (suc zero) t = con (quote inj₁) [ vArg t ]
    inj (suc n)    t = con (quote inj₂) [ vArg (inj n t) ]
genFromClauses _ _ _ _ _ = typeError [ strErr "Number of constructors does not match the given Poly definition." ]

genIso : (from : Name) → (to : Name)
       → (target : Name) → Poly → TC ⊤
genIso from to target F =
  do definition ← getDefinition target
     --debugPrint "meta" 5 (strErr "typ: " ∷ [ termErr (def target []) ])
     qF ← quoteTC F
     case definition of λ where
       (data-type pars cs) → do
         cls ← genFromClauses from (def target []) cs F F
         --debugPrint "meta" 5 [ strErr (showClauses cls) ]
         declareDef (vArg from)
                  $ pi (vArg $ def target [])
                       (abs "_" $ def (quote μ) [ vArg qF ])
         defineFun from cls
       _ → typeError (nameErr target ∷ [ strErr " is not a datatype." ])

unquoteDecl μfromList = genIso μfromList (quote tt) (quote ListN) (ListF ℕ)

a : μ (ListF ℕ)
a = μfromList (consN 0 (consN 1 nilN))

module _ (data₀ : Name) (fun₀ : Name) (F : Poly) (ϕ : Name) (from : Name) (to : Name) where

  genMonoTypes : Mono → TC (List Type)
  genMonoTypes ∅        = return []
  genMonoTypes I        = return [ def data₀ [] ]
  genMonoTypes (K A)    = ⦇ [ quoteTC A ] ⦈
  genMonoTypes (M ⊗ M') = ⦇ genMonoTypes M ++ genMonoTypes M' ⦈

  genType : TC Type
  genType = do typ' ← replaceμ ϕ <$> getType fun₀
               qF   ← quoteTC F
               pos  ← freshName "_"
               declarePostulate (vArg pos) typ'
               t    ← inferType (def pos [ vArg qF ]) >>= normalise
               --μtyp ← inferType (def ν [ vArg qF ]) >>= normalise
               --debugPrint "meta" 5 [ termErr μtyp ]
               return t

  -- generate the clauses with two list of types that appear in the patterns,
  -- between which the deconstructed target datatype should be in the middle.
  -- A clause:
  -- f : A → B → μ F → C
  -- f : A → B → D → C
  -- fun w x (...) y =
  -- fun w x (by₁ z₁ z₂) y = by₂ z₁ z₂
  -- is implicitly:
  -- fun [ w : T₁ , x : T₂ , z₁ : T₃ , z₂ : T₄ , y : T₅ ]             --→ Telescope
  --  ╭─ (var 4 , var 3 , ⟦ by₁ ⟧ [ var 2 , var 1 ] , var 0) --→ Pattern
  --  │  (⟦ by₂ ⟧ [ var 2 , var 1 ])                         --→ Term
  --  │
  --  ╰─── originally (var 3 , var 2 , var _ , var 0)
  genClauses : Telescope → Telescope
             → Poly → List Name → TC Clauses
  genClauses _ _ _ [] = return []
  genClauses _ _ [] _ = return []
  genClauses tel₁ tel₂ (M ∷ G) (n ∷ ns) = do
    typsᴹ ← genMonoTypes M
    qF    ← quoteTC F
    let len₁ = length tel₁
        lenᴹ = length typsᴹ
        len₂ = length tel₂
        lenTotal = len₁ + lenᴹ + len₂
    ty ← getType fun₀ >>= normalise
    debugPrint "meta" 5 [ termErr ty ]
    let term = --← normalise $
             def fun₀ (vArg qF
                      ∷ weakenArgs (lenᴹ + len₂) (vars tel₁)
                      ++ [ vArg (def from [ conTerm n ]) ]
                      ++ vars tel₂)
    --debugPrint "meta" 5 [ termErr term ]
    -- should be normalised from "fold (ListF ℕ) e f (fromList ?)"
    -- then traverse and search for a pattern normalised from
    -- "fold (ListF ℕ) e f ?" and replace it with the realized fold
    -- Apparently, some meta fromList should be derived first.

      -- $ con n (vArg qF ∷ weakenArgs (lenᴹ + len₂) (vars len₁)
      --           ++ [ conTerm n ]
      --           ++ vars len₂)
    --debugPrint "meta" 5 [ strErr $ "RHS of the clause: " <> (showTerm term) ]
    cls ← genClauses tel₁ tel₂ G ns
    return $ clause (tel₁
                      ++ map (_,_ "_" ∘ vArg) typsᴹ
                      ++ shiftTel lenᴹ tel₂)
                    (weakenArgPats (lenᴹ + len₂) (pats tel₁)
                      ++ weakenArgPats len₂ [ conPat n ]
                      ++ (pats tel₂))
                    term
           ∷ cls
    where

      pats : Telescope → List (Arg Pattern)
      pats = foldr (λ { (_ , arg i _) xs → arg i (var (length xs)) ∷ xs}) []

      vars : Telescope → List (Arg Term)
      vars = foldr (λ { (_ , arg i _) xs → arg i (var (length xs) []) ∷ xs}) []

      varPats : List (Arg Pattern)
      varPats = fromMonoGenArgs M 0 λ _ → var

      varTerms : List (Arg Term)
      varTerms = fromMonoGenArgs M 0 λ _ n → var n []

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
  genFun : Name → TC _
  genFun fun₁ = do t ← genType
                   declareDef (vArg fun₁) t
                   debugPrint "meta" 5 (strErr "Type of f: " ∷ [ termErr t ])
                   qF ← (quoteTC F) >>= normalise
                   T  ← inferType (def fun₀ [ vArg qF ]) >>= normalise
                   let tel = piToTel T
                       tel₁ , xtel₂ = break (≟-μ qF) tel
                   tel₂ ← case xtel₂ of λ where
                     [] → typeError [ strErr "no datatype found in the definition." ]
                     (_ ∷ xs) → return xs
                   debugPrint "meta" 5
                              [ case tel₁ of (λ where
                                  [] → strErr "tel₁ is empty."
                                  t  → strErr $ "tel₁: " <> showTel t) ]
                   definition ← getDefinition data₀
                   cs ← case definition of λ where
                     (data-type _ cs) → return cs
                     _ → typeError (strErr "Given name " ∷ nameErr data₀ ∷ [ strErr " is not a datatype."])
                   cls ← genClauses tel₁ tel₂ F cs
                   debugPrint "meta" 5 [ strErr $ "Clauses: " <> (showClauses cls) ]
                   defineFun fun₁ cls
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
-- genFun : (data₀ : Name) (fun₀ : Name) (F : Poly) (ϕ : Name) (from : Name) (to : Name) → Name → TC _

ϕ : Poly → Set
ϕ _ = ListN

--foldN : {X : Set} (z : X) (f : ℕ → X → X) → ListN → X
--foldN {X} z f nilN = fold (ListF ℕ) {X} z f (μfromList nilN)
--foldN {X} z f (consN z₁ m) = fold (ListF ℕ) {X} z f (μfromList (consN z₁ m))

unquoteDecl foldN = genFun (quote ListN) (quote fold) (ListF ℕ) (quote ϕ) (quote μfromList) (quote tt) foldN

foldTyp : TC _
foldTyp = do t ← getDefinition (quote foldN)
             case t of λ where
               (function cs) → debugPrint "meta" 5 [ strErr (showClauses cs) ]
               _ → typeError [ strErr "" ]

unquoteDecl = foldTyp

sum : ListN → ℕ
sum = foldN 0 _+_

--genPat : Name → Poly → TC Term
--genPat n T = {!!}


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
  --  varPats M = fromMonoGenArgs M 0 λ _ → var

  --  conPat : Name → Arg Pattern
  --  conPat ν = vArg (con ν (varPats M))

  --  varTerms : List (Arg Term)
  --  varTerms = fromMonoGenArgs M 0 λ _ n → var n []

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
