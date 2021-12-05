{-# OPTIONS -v meta:5 #-}
open import Level using (0ℓ)

open import Prelude
  hiding (_<$>_)

open import Universe.PolyUniverse
open import Prelude hiding (_<$>_)
open import Utils

open import Reflection.TypeChecking.Monad.Syntax
open import Reflection.Term as Term
  hiding (_≟_)
open import Reflection.DeBruijn
import      Reflection.Traversal {id} (record { pure = id ; _⊛_ = id }) as Trav
import      Reflection.Traversal {TC} (record { pure = return
                                         ; _⊛_ = λ A→Bᵀ Aᵀ → A→Bᵀ >>= λ A→B
                                         → bindTC Aᵀ (return ∘ A→B) }) as TravTC

open import Universe.PolyUniverse

piToTel : Term → Telescope
piToTel (pi (arg i x) (abs s y)) = (s , arg i x) ∷ piToTel y
piToTel t = [] -- ignoring the last term in a pi chain

fromMonoGenArgs : {X : Set} → Mono → ℕ → (Mono → ℕ → X) → List (Arg X)
fromMonoGenArgs ∅        n f = []
fromMonoGenArgs I        n f = [ vArg (f I n) ]
fromMonoGenArgs Κ@(K _)  n f = [ vArg (f Κ n) ]
fromMonoGenArgs (M ⊗ M') n f = let ms = fromMonoGenArgs M' n f
                                in fromMonoGenArgs M (n + length ms) f ++ ms

--???: Is weakening needed?
⟪_⟫ : Mono → Type → Type → TC Type
⟪_⟫ ∅        s t = return t
⟪_⟫ I        s t = return (pi (vArg s) (abs "_" t))
⟪_⟫ (K A)    s t = do a ← quoteTC A --?
                      return (pi (vArg a) (abs "_" t))
⟪_⟫ (M ⊗ M') s t = ⟪ M' ⟫ s t >>= ⟪ M ⟫ s

-- the corresponding constructor type of a Mono
toConDef : Mono → Name → TC Type
toConDef M ν = ⟪ M ⟫ (def ν []) (def ν [])

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
                  {onDef = λ _ name → if does (name ≟ quote μ)
                                        then ν
                                        else name})
               (zero Trav., [])

breakAt : Type → Telescope → Telescope × Telescope
breakAt target tel = break eq tel -- break eq tel
  where eq : (a : String × Arg Type) → Dec (unArg (snd a) ≡ target)
        eq (_ , (arg _ x)) = x ≟ target
        
weakenArgPats : ℕ → List (Arg Pattern) → List (Arg Pattern)
weakenArgPats = map ∘ weakenFrom′ Trav.traversePattern 0
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

-- ν is the name of the function to be translated, e.g. fold.
-- F is the polynomial definition of the target datatype that should appears in the type of ν.
-- The target datatype is assumed to be represented by μ : Poly → Set.
-- ϕ is the transformation to be substituted for μ.
parseCon : Name → Name → Mono → TC Telescope
parseCon dataName conName M = do
  t  ← getType conName
  tᴹ ← toConDef M dataName
  let d   = (removeStr t) ≟ (removeStr tᴹ)
      tel = piToTel t
  if (does d)
    then return tel
    else typeError (strErr "Given datatype constructor: "
                   ∷ termErr t
                   ∷ strErr " and the type of the corresponding constructor of the Mono definition "
                   ∷ termErr tᴹ
                   ∷ strErr " does not match."
                   ∷ [])
  where
    mutual
      removeStr : Term → Term
      removeStr (var x args) = var x (removeStrArgs args)
      removeStr (con c args) = con c (removeStrArgs args)
      removeStr (def f args) = def f (removeStrArgs args)
      removeStr (lam v (abs s x)) = lam v (abs "_" (removeStr x))
      removeStr (pat-lam cs args) = pat-lam cs (removeStrArgs args)
      removeStr (Π[ s ∶ arg i x ] y) = Π[ "_" ∶ arg i (removeStr x) ] removeStr y
      removeStr t = t
      --for termination check
      removeStrArgs : List (Arg Term) → List (Arg Term)
      removeStrArgs [] = []
      removeStrArgs (x ∷ as) = removeStrArg x ∷ removeStrArgs as

      removeStrArg : Arg Term → Arg Term
      removeStrArg (arg i x) = arg i (removeStr x)

-- fromList : ListN → μ (ListF ℕ)
-- inj₁ _
-- inj₂ (inj₁ _)
-- inj₂ (inj₂ (inj₁ _))
-- ...
genFromClauses : Name → Name → List Name → Poly → Poly → TC Clauses
genFromClauses _ _ [] [] _ = return []
genFromClauses funName dataName (conName ∷ conNames) (M ∷ Ms) F = do
  tel ← parseCon dataName conName M
  let len = length tel
      term = prodTerm (recurse tel (def dataName [])) len
      cl = clause
             tel
             [ vArg $ con conName (pats tel) ]
           $ con (quote μ.con)
                 [ vArg $ inj (length F ∸ length Ms) term ]
  --debugPrint "meta" 5 [ strErr (showClause cl) ]
  cls ← genFromClauses funName dataName conNames Ms F
  return (cl ∷ cls)
  where
    pats : Telescope → List (Arg Pattern)
    pats = foldr (λ { (_ , arg i _) xs → arg i (var (length xs)) ∷ xs}) []

    recurse : Telescope → Type → Term → Term
    recurse tel target t@(var x args) =
      case lookupCxt tel x of λ where
        (just (_ , arg _ typ)) → if does (typ ≟ target) then
                                   def funName [ vArg t ]
                                 else t
        nothing → t
    recurse tel _ t = t

    prodTerm : (Term → Term) → ℕ → Term
    prodTerm f = snd ∘
                 fold (0 , quoteTerm tt)
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
    inj (suc zero) t = con (quote inl) [ vArg t ]
    inj (suc n)    t = con (quote inr) [ vArg (inj n t) ]
genFromClauses _ _ _ _ _ = typeError [ strErr "Number of constructors does not match the given Poly definition." ]

genIso : (from : Name) → (to : Name)
       → (target : Name) → Poly → TC ⊤
genIso from to target F =
  do definition ← getDefinition target
     --debugPrint "meta" 5 (strErr "typ: " ∷ [ termErr (def target []) ])
     qF ← quoteTC F
     case definition of λ where
       (data-type pars cs) → do
         cls ← genFromClauses from target cs F F
         --debugPrint "meta" 5 [ strErr (showClauses cls) ]
         declareDef (vArg from)
                  $ pi (vArg $ def target [])
                       (abs "_" $ def (quote μ) [ vArg qF ])
         defineFun from cls
       _ → typeError (nameErr target ∷ [ strErr " is not a datatype." ])

unquoteDecl μfromList = genIso μfromList (quote tt) (quote ListN) (ListF ℕ)

--fromList′ : ListN → μ (ListF ℕ)
--fromList′ nilN = con (inj₁ tt)
--fromList′ (consN z xs) = con (inj₂ (inj₁ (z , (fromList′ xs))))
--
--iso : ∀ {xs} → μfromList xs ≡ fromList′ xs
--iso {nilN} = _≡_.refl
--iso {consN z xs} = {!!}

-- Only one kind of difference is acceptable.
S&Rs : Term → (Term → Term) → List (Arg Term) → List (Arg Term) → List (Maybe Term)
S&R : Term → (Term → Term) → Term → Term → Maybe Term

{-# TERMINATING #-}
S&Rs inner f [] [] = []
S&Rs inner f (arg _ x ∷ xs) (arg _ y ∷ ys) = S&R inner f x y ∷ S&Rs inner f xs ys
S&Rs inner f _ _ = []

S&R inner f x y =
  if (does $ y ≟ inner)
    then just (f x)
  else case (x , y) of λ where
         (var m args₁ , var n args₂) →
           if suc m == n
             then maybes (S&Rs inner f args₁ args₂)
             else nothing
         (con c args₁ , con d args₂) →
           if (does (c ≟ d))
             then (maybes $ S&Rs inner f args₁ args₂)
             else nothing
         (def c args₁ , def d args₂) →
           if (does (c ≟ d))
             then (maybes $ S&Rs inner f args₁ args₂)
             else nothing
         (_ , _) → nothing

{-# TERMINATING #-}
S&Rrec : Term → (Term → Term) → Term → Term → Maybe Term
S&Rrec inner f term pat = S&R inner f term pat
                      <∣> (case term of λ where
                            (var x args) → just (var x $ S&Rargs args)
                            (con c args) → just (con c $ S&Rargs args)
                            (def f args) → just (def f $ S&Rargs args)
                            (lam v t) → just (lam v (map fromMaybeId t))
                            t → just t)
  where
    fromMaybeId : Term → Term
    fromMaybeId t = fromMaybe t (S&Rrec inner f t pat)

    S&Rargs : List (Arg Term) → List (Arg Term)
    S&Rargs args = map fromMaybeId args

module _ (data₀ : Name) (fun₀ : Name) (F : Poly) (ϕ : Name)
         (from : Name) (to : Name) (fun₁ : Name) where

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
  -- fun [ w : T₁ , x : T₂ , z₁ : T₃ , z₂ : T₄ , y : T₅ ]    --→ Telescope
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
    ty ← getType fun₀ >>= normalise
    debugPrint "meta" 5 [ termErr ty ]
    let term x len by =
          def fun₀ (vArg qF
                   ∷ weakenArgs (len + len₂ + by) (vars tel₁)
                   --++ [ vArg (def from [ conTerm n ]) ]
                   ++ [ vArg x ]
                   ++ weakenArgs by (vars tel₂))
        tel xs len = (tel₁ ++ xs ++ shiftTel len tel₂)
        recPat : Term
        recPat = term (var 0 []) lenᴹ 1
        recResult : Term → Term
        recResult x = def fun₁ (weakenArgs (lenᴹ + len₂) (vars tel₁)
                               ++ [ vArg x ]
                               ++ vars tel₂)
        term' = term (def from [ conTerm n ]) lenᴹ 0
    let tel' = (tel (map (_,_ "_" ∘ vArg) typsᴹ) lenᴹ)
        pat = (weakenArgPats (lenᴹ + len₂) (pats tel₁)
                ++ weakenArgPats len₂ [ conPat n ]
                ++ (pats tel₂))
    debugPrint "meta" 5 [ strErr $ "Telescope: " <> (show tel') ]
    t ← inContext
          (map snd $ reverse tel')
          (do t' ← normalise $ term (def from [ conTerm n ]) lenᴹ 0
              r ← normalise (vLam "hole" recPat)
              r' ← case r of λ where
                     (lam x (abs _ t)) → return t
                     _ → typeError [ strErr "not lambda" ]
              --debugPrint "meta" 5 [ strErr $ "Unreplaced Term: " <> (showTerm t') ]
              --debugPrint "meta" 5 [ strErr $ "Pattern Term: " <> (showTerm r) ]
              res ← maybe′ return
                  (typeError [ strErr "Failed to parse recursive definition." ])
                  (S&Rrec (var 0 []) recResult t' r')
              res' ← normalise $ Trav.traverseTerm
                        (record Trav.defaultActions {
                           onDef = λ _ x → if (does $ x ≟ from)
                                             then (quote id)
                                             else x
                        })
                        (0 Trav., [])
                        res
              --debugPrint "meta" 5 [ strErr $ "Fixed Replaced Term: " <> (showTerm res') ]
              return res')
    --debugPrint "meta" 5 [ strErr ("Replaced Term: " <> showTerm t) ]
    -- should be normalised from "fold (ListF ℕ) e f (fromList ?)"
    -- then traversed and searched for a pattern normalised from
    -- "λ x → fold (ListF ℕ) e f x" and replaced by the realized fold
    -- Apparently, some meta fromList should be derived first.
    cls ← genClauses tel₁ tel₂ G ns
    return $ clause tel'
                    pat
                    t --(term (def from [ conTerm n ]) lenᴹ 0)
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
  genFun : TC _
  genFun = do t ← genType
              declareDef (vArg fun₁) t
              debugPrint "meta" 5 (strErr "Type of f: " ∷ [ termErr t ])
              qF ← quoteTC F >>= normalise
              T  ← inferType (def fun₀ [ vArg qF ]) >>= normalise
              let tel = piToTel T
                  tel₁ , xtel₂ = break (≟-μ qF) tel
              tel₂ ← case xtel₂ of λ where
                [] → typeError [ strErr "no datatype found in the definition." ]
                (_ ∷ xs) → return xs
              debugPrint "meta" 5
                         [ case tel₁ of (λ where
                             [] → strErr "tel₁ is empty."
                             t  → strErr $ "tel₁: " <> show t) ]
              definition ← getDefinition data₀
              cs ← case definition of λ where
                (data-type _ cs) → return cs
                _ → typeError (strErr "Given name " ∷ nameErr data₀ ∷ [ strErr " is not a datatype."])
              cls ← genClauses tel₁ tel₂ F cs
              debugPrint "meta" 5 [ strErr $ "Clauses: " <> (show cls) ]
              defineFun fun₁ cls
              return tt
    where
      -- The decidable equality should identify something like (μ (∅ ∷ (K ℕ ⊗ I) ∷ []))
      ≟-μ : (qF : Type) → (x : String × Arg Type)
          → Dec (unArg (snd x) ≡ def (quote μ) [ vArg qF ])
      ≟-μ qF (_ , arg _ x) = x ≟ def (quote μ) [ vArg qF ]


--------
-- Examples, this part should be user-defined.
-- A ϕ transformation from the univserse to native datatype should be defined.
-- For example, A (ListF ℕ) in Poly should be mapped to native (List ℕ).
-- genFun : (data₀ : Name) (fun₀ : Name) (F : Poly) (ϕ : Name) (from : Name) (to : Name) → Name → TC _

ϕ : Poly → Set
ϕ _ = ListN

--application of lambda cannot be reflected.
unquoteDecl foldN = genFun (quote ListN) (quote fold) (ListF ℕ) (quote ϕ) (quote μfromList) (quote tt) foldN

foldN' : {X : Set} (z : X) (f : ℕ → X → X) → ListN → X
foldN' {X} z f nilN = fold (ListF ℕ) {X} z f (μfromList nilN)
foldN' {X} z f (consN x m) = f x (foldN' z f m)

sum : ListN → ℕ
sum = foldN 0 _+_

sum' : ListN → ℕ
sum' nilN = 0
sum' (consN z xs) = z + sum' xs

sumEq : ∀ xs → sum xs ≡ sum' xs
sumEq nilN = _≡_.refl
sumEq (consN z xs) = cong (_+_ z) (sumEq xs)
