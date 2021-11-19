{-# OPTIONS -v meta:5 #-}
--{-# OPTIONS -v tc.data.con:16 #-}
{-# OPTIONS -v tc.unquote.def:11 #-}
--{-# OPTIONS -v tc.data.sort:21 #-}
--{-# OPTIONS -v tc.data.con.comp:6 #-}
--{-# OPTIONS -v tc.conv.term:21 #-}

open import Prelude
open import Tactic.MonoidSolver
open import Data.Nat.Properties
  using (+-0-monoid)
  
import Reflection.Name
import Reflection.Term
open import Agda.Builtin.Reflection

lemma : ∀ x y z → (x + y) + z ≡ x + (y + z)
lemma x y z = solve +-0-monoid


_ : quoteTerm 1 ≡ lit (nat 1)
_ = refl

_ : quoteTerm zero ≡ con (quote zero) []
_ = refl

_ : quoteTerm (suc zero) ≡ con (quote suc) (vArg (con (quote zero) []) ∷ [])
_ = refl

_ : quoteTerm ℕ ≡ def (quote ℕ) []
_ = refl

_ : Name
_ = quote _≡_

one = 1

_ : quoteTerm one ≡ def (quote one) []
_ = refl

_ : Name
_ = quote one

plus-to-times′ : Term → Term → TC _
plus-to-times′ (def (quote _+_) (a ∷ b ∷ [])) hole = do
  debugPrint "meta" 2 [ strErr "hello world" ]
  unify hole (def (quote _*_) (a ∷ b ∷ []))
plus-to-times′ v hole = unify hole v

macro
  plus-to-times : Term → (Term → TC ⊤)
  plus-to-times (def (quote _+_) (a ∷ b ∷ [])) hole = unify hole (def (quote _*_) (a ∷ b ∷ []))
  plus-to-times v hole = unify hole v

thm : (a b : ℕ) → plus-to-times (a + b) ≡ a * b
thm a b = refl

macro
  isMacro? : Name → Term → TC ⊤
  isMacro? id hole = do
    isMacro id >>= λ where
      false → debugPrint "meta" 2 (nameErr id ∷ [ strErr " is NOT a macro" ])
      true  → debugPrint "meta" 2 (nameErr id ∷ [ strErr " is a macro" ])
    unify hole (quoteTerm tt)

macro
  showTerm′ : Term → Term → TC ⊤
  showTerm′ t hole = do
    debugPrint "meta" 2 [ termErr t ]
    unify hole (quoteTerm tt)

macro
  showType : Name → Term → TC _
  showType t hole = do
               t2 ← getType t
               --t3 ← inferType t2 -- Term → Type
               debugPrint "meta" 2 [ termErr t2 ]
               unify hole (quoteTerm tt)

--data RGB : Set where
--  Red Green Blue : RGB

--“ℓ₀” : Arg Term
--“ℓ₀” = hArg (def (quote Level.zero) [])

--“RGB” : Arg Term
--“RGB” = hArg (def (quote RGB) [])
--
--“Red” : Arg Term
--“Red” = vArg (con (quote Red) [])

--unquoteDecl IsRed =
--  do ty ← quoteTC (RGB → Set)
--     declareDef (vArg IsRed) ty
--     defineFun IsRed [ Reflection.Clause.clause
--                         [ ("x" , vArg (def (quote RGB) [])) ]
--                         [ vArg (Pattern.var 0) ]
--                         (def (quote _≡_) (“ℓ₀” ∷ “RGB” ∷ “Red” ∷ vrv 0 [] ∷ [])) ]

data ListA (A : Set) : Set where
  nil  : ListA A
  cons : A → ListA A → ListA A

data ListB (A : Set) : Set where
  nil'  : ListB A
  cons' : A → ListB A → ListB A

--C : ⊤
--C = showTerm′ (quoteTerm ({A : Set} → ListA A → ℕ))

data ℕ2 : Set where
  zero : ℕ2

--zero : Set

-- quoting an ambiguous construnctor
--B : ⊤
--B = showTerm′ {!!}

--_ = zero

--D : ⊤
--D = showTerm′ (quoteTerm ((A : Set) → (n : ℕ) → Set))

-- nil : λ List_ 0
isNilType : Type → Bool
isNilType (pi (hArg (agda-sort (Sort.lit 0)))
              (abs _ (def _ (vArg (var 0 []) ∷ [])))) = true
isNilType _ = false

-- (List A) B
isConsType : Type → Bool
isConsType (pi (hArg (agda-sort (Sort.lit 0)))
               (abs _ (pi (vArg (var 0 []))
                          (abs _ (pi (vArg (def a (vArg (var 1 []) ∷ [])))
                                     (abs _ (def b (vArg (var 2 []) ∷ []))))))))
                                       = does (a Reflection.Name.≟ b)
isConsType _ = false

macro
  isNilMacro : Name → Term → TC _
  isNilMacro n hole = do
                 t ← getType n
                 case isNilType t of λ where
                   false → debugPrint "meta" 2  (nameErr n ∷ strErr " is not Nil!" ∷ [])
                   true  → debugPrint "meta" 2  (nameErr n ∷ strErr " is Nil!" ∷ [])

macro
  isConsMacro : Name → Term → TC _
  isConsMacro n hole = do
                  t ← getType n
                  case isConsType t of λ where
                    false → debugPrint "meta" 2  (nameErr n ∷ strErr " is not Cons!" ∷ [])
                    true  → debugPrint "meta" 2  (nameErr n ∷ strErr " is Cons!" ∷ [])
--A : ⊤
--A = showTerm′ (quoteTerm ({A : Set} → A → ListA A → ListA A))

--A₁ : ⊤
--A₁ = isNilMacro nil
--
--A₂ : ⊤
--A₂ = isNilMacro cons
--
--B₁ : ⊤
--B₁ = isConsMacro nil
--
--B₂ : ⊤
--B₂ = isConsMacro cons
--
--notcons : {A : Set} → A → ListB A → ListA A
--
--B₃ : ⊤
--B₃ = isConsMacro notcons

macro
  showCl : Name → Term → TC _
  showCl n hole = do getDefinition n >>= λ where
                       (function (b ∷ s ∷ []))
                         → debugPrint "meta" 2 (strErr "These are the clauses of function "
                                                  ∷ nameErr n
                                                  ∷ strErr " :\n"
                                                  ∷ strErr (showClause b <> "\n" <> showClause s)
                                                  ∷ [])
                       _ → return tt
                     unify hole (quoteTerm tt)

macro
  showNorm : Name → Name → Term → TC _
  showNorm n s hole = do norm ← normalise (def n (vArg (quoteTerm ℕ.zero)
                                                    ∷ vArg (def s [ vArg (quoteTerm ℕ.zero) ])
                                                    ∷ []))
                         debugPrint "meta" 2 [ termErr norm ]
                         unify hole (quoteTerm tt)

plus' : ℕ → ℕ → ℕ
plus' a b = a + b

suc'' : ℕ → ℕ
suc'' n = suc (suc n)

shown : ⊤
shown = showNorm plus' suc''


data VecA (A : Set) : (n : ℕ) → Set where
  nilV  : VecA A 0
  consV : {n : ℕ} → (a : A) → VecA A n → VecA A (n + 1)

-- Determining if something is a list and return its nil and cons.
isList : Name → TC (Bool × Name × Name)
isList n = getDefinition n >>= λ where
             (data-type 1 (b ∷ s ∷ []))
               → do bt ← getType b
                    st ← getType s
                    return (isNilType bt ∧ isConsType st , b , s)
             _ → return (false , n , n)

-- For a clause to be a base, it must be of the form `h nil = c`.
isBase : Name → Clause → TC (Bool × Term)
isBase n (clause
           (_ ∷ [])
           (hArg (var 0)
              ∷ (vArg (con c []))
              ∷ [])
           t)
           = return (does (n Reflection.Name.≟ c) , t)
isBase _ _ = return (false , unknown)

-- For a clause to be a step, it must be of the form `h (cons a x) = f a (h x)`.
-- s: the 'step' constructor in question
-- n: the 'step' part of an F-algebra, i.e. f in [c , f]
isStep : Name → Name → Name → Clause → TC (Bool × Term)
isStep func
       con₂
       stepFunc
       (clause
          (_ ∷ _ ∷ _ ∷ [])
          ((hArg (Pattern.var 2))
              ∷ (vArg (con c (vArg (Pattern.var 1)
                                ∷ vArg (Pattern.var 0)
                                ∷ [])))
              ∷ [])
          t) = isStep′ t >>= λ b → return (does (con₂ Reflection.Name.≟ c) ∧ b , t)
                 where isStep′ : Term → TC Bool
                       isStep′ t =
                         do t₁ ← normalise t
                            t₂ ← normalise (def stepFunc
                                                (vArg (var 1 [])
                                                   ∷ vArg (def func [ vArg (var 0 []) ])
                                                   ∷ []))
                            return (does (t₁ Reflection.Term.≟ t₂))
isStep _ _ _ _ = return (false , unknown)

lengthA : {A : Set} → ListA A → ℕ
lengthA nil = 0
lengthA (cons x xs) = suc (lengthA xs)
-- f a b = suc b
-- suc (lengthA xs) == f x (lengthA xs)
--lenCl : ⊤
--lenCl = showCl lengthA

-- How to describe the relation between clauses of the same function?
-- If f is a fold, we should get 
--isFold : Name → Name → Name → TC (Bool × Name × Name × Name)
--isFold f stepFunc l =
--  isList l >>= λ where
--    (true , nilCon , consCon)
--      → getType f >>= λ where
--          (pi (hArg (agda-sort (Sort.lit 0)))
--              (abs _ (pi (vArg (def t (vArg (var 0 []) ∷ [])))
--                         (abs _ (def idx [])))))
--            → getDefinition f >>= λ where
--                (function (cls₁ ∷ cls₂ ∷ []))
--                  → do (b₁ , t₁) ← isBase nilCon cls₁
--                       (b₂ , t₂) ← isStep f consCon stepFunc cls₂
--                       return (b₁ ∧ b₂ ∧ does (t Reflection.Name.≟ l) , {!!})
--                  --→ return (isBase n b ∧ isStep c s , n , c , idx)
--                _ → return (false , l , l , l)
--          _ → return (false , l , l , l)
--    _ → return (false , l , l , l)
--
--VecC : (A : Set) → (n : ℕ) → Set
--VecC A zero = ⊤
--VecC A (suc n) = A × VecC A n
--
--data Term' (fv : ℕ) : Set where
--  var : Data.Fin.Fin fv → Term' fv
--  app : Term' fv → Term' fv → Term' fv
--  lam : Term' (suc fv) → Term' fv

-- data VecD (A : Set) : (r : Real) → Set 
--   nilD : VecD A 0.0
--   consD : A → VecD A → VecD A (mean ?)

--sc : ⊤
--sc = showCl VecC

--V : ⊤
--V = showTerm′ (quoteTerm {!!})

stepLength : {A : Set} → A → ℕ → ℕ
stepLength _ n = suc n

--macro
--  withFuncListToVec : Name → Name → Name → Term → TC _
--  withFuncListToVec f stepFunc l hole =
--    do isFold f stepFunc l >>= λ where
--         (true , ni , co , idx)
--           → do newVec  ← freshName "newVec"
--                declareDef (vArg newVec) (pi (vArg (agda-sort (Sort.lit 0)))
--                                             (abs "A" (pi (vArg (def idx []))
--                                                          (abs "n" (agda-sort (Sort.lit 0))))))
--                defineFun newVec ( clause ( ("A" , (vArg (quoteTerm Set)))
--                                          ∷ ("n" , (vArg (quoteTerm idx)))
--                                          ∷ [])
--                                          (vArg (var 1) ∷ vArg (con {!!} {!!}) ∷ [])
--                                          (quoteTerm ⊤)
--                                 ∷ clause ( ("A" , (vArg (quoteTerm Set)))
--                                          ∷ ("n" , (vArg (quoteTerm idx)))
--                                          ∷ [])
--                                          (vArg (var 1) ∷ vArg (con {!!} {!!}) ∷ [])
--                                          (def (quote _×_) (vArg {!!} ∷ vArg (def newVec ({!!} ∷ {!!} ∷ [])) ∷ []))
--                                 ∷ [])
--         _ → return tt
--       unify hole (quoteTerm tt)
--  withFuncListToVec f n hole = isList n >>= λ where
--                                 false → debugPrint "meta" 2 (nameErr n ∷ strErr " is not List!" ∷ [])
--                                 true  → isFold f n >>= λ islength →
--                                         case islength of λ where
--                                           (false , _) → debugPrint "meta" 2 ( nameErr f
--                                                                           ∷ strErr " is not a fold on "
--                                                                           ∷ nameErr n
--                                                                           ∷ strErr "!"
--                                                                           ∷ [] )
--                                           (true , par) → {!!}

showCs : List Name → TC ⊤
showCs [] = debugPrint "meta" 2 [ strErr "All constructors printed." ]
showCs (x ∷ l) = getType x >>= λ c →
  debugPrint "meta" 2 (strErr "Constructor "
                         ∷ nameErr x
                         ∷ strErr (" is defined as:\n" <> (showTerm c))
                         ∷ []) >>
  showCs l

showDef′ : Name → TC _
showDef′ n = do
  getDefinition n >>= λ where
    d@(data-type _ cs) → do
      debugPrint "meta" 2 [ strErr (showDefinition d) ]
      showCs cs
    d → debugPrint "meta" 2 [ strErr (showDefinition d) ]
  getType n >>= λ x →
    debugPrint "meta" 2 (strErr "The type of the declared datatype '"
                        ∷ nameErr n
                        ∷ strErr "' is: "
                        ∷ termErr x
                        ∷ [])

liftNames : List (TC Name × Term) → TC (List (Name × Term))
liftNames [] = return []
liftNames ((tn , t) ∷ l) = do n   ← tn
                              res ← liftNames l
                              return ((n , t) ∷ res)

getConNames : List (String × (Name → Term)) → TC (List (Name × Term))
getConNames [] = return []
getConNames ((conName , f) ∷ ss) = do fName ← freshName conName
                                      ss    ← getConNames ss
                                      return ((fName , (f fName)) ∷ ss)

macro
  newData : String → Type → Type → (Name → List (String × (Name → Term))) → Term → TC _
  newData s t u f hole = do
    --debugPrint "meta" 2 ([ strErr "yo" ])
    newName ← freshName s
    declareData (vArg newName) u t
    --let conNames = map (λ (s , t) → freshName s , t) (f newName)
    let conNames = f newName
    cs ← getConNames (zip (map proj₁ conNames) (map proj₂ conNames))
    defineData newName cs
    getType newName >>= λ x →
      debugPrint "meta" 2 (strErr "The type of the declared datatype '"
                             ∷ nameErr newName
                             ∷ strErr "' is: "
                             ∷ termErr x
                             ∷ [])
    getDefinition newName >>= λ where
      d → debugPrint "meta" 2 [ strErr (showDefinition d) ]
    showDef′ newName
    unify hole (quoteTerm tt)

B : ⊤
--B = newData "newtype"
--            (pi (vArg (quoteTerm ℕ)) (abs "idx" (quoteTerm Set)))
--            (quoteTerm (Set → Set))
--            λ dataName → [ "conpi" , (λ conName → con conName {!!}) ]
B = newData "newtype"                                             -- Name of the new datatype.
            (pi (vArg (quoteTerm ℕ)) (abs "idx" (quoteTerm Set))) -- Type of the datatype.
            (quoteTerm (Set → Set))                               -- Types of parameters of the datatype. The type it ends in is ignored.
            (λ dataName →                                         -- List of constructors and their respective types. The declared name can be used.
                 [ "conpi" , (λ _ → pi (vArg (quoteTerm Set))
                                       (abs "A" (pi (vArg (quoteTerm ℕ))
                                                    (abs "n" (def dataName (vArg (var 1 [])
                                                                              ∷ vArg (var 0 [])
                                                                              ∷ [])))))) ])

macro
  showDef : Name → Term → TC ⊤
  showDef n hole = do
    showDef′ n
    unify hole (quoteTerm tt)

data ParTest (P : Set) : Set where
  PP : ℕ → ParTest P

C : ⊤
C = showType PP
