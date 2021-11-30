{-# OPTIONS --safe #-}
module Prelude where 

--open import Data.Nat       public
--  hiding (_≟_; _⊔_; _^_)
  
open import Data.Fin.Base       public
  using (Fin; fromℕ; fromℕ<; fromℕ<″)
--open import Data.List.Base public
--  using (List; []; _∷_; _++_; length; break; [_]; concat; zip; zipWith; foldr; lookup; reverse)

-- Reflection related
open import Reflection     public
  hiding (_≟_; showTel; showClauses)
open import Reflection.Argument     public
  using (unArg)

------------------------------------------------------------------------------
-- Built-in modules 
open import Agda.Primitive                public
open import Agda.Builtin.Unit             public
open import Agda.Builtin.String           public
  using (String)
  renaming (primStringAppend to infixr 5 _<>_)
open import Agda.Builtin.Reflection       public
  using (declareData; defineData)

--
open import Prelude.Function              public
-- Data Types
open import Prelude.Empty                 public
open import Prelude.Bool                  public
open import Prelude.Nat public
  hiding (_==_)
open import Prelude.Maybe                 public
  hiding (map)
open import Prelude.List                  public
  hiding (map)
open import Prelude.Sigma                 public
open import Prelude.Sum                   public
--open import Prelude.List                  public
--  hiding (map)

open import Prelude.Relation              public
open import Prelude.PropositionalEquality public

-- Type classes
open import Prelude.Show                  public
open import Prelude.Equality              public
open import Prelude.Functor               public

open import Prelude.Level                 public
