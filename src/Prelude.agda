module Prelude where 

open import Function       public
open import Function.Base  public
  using (case_of_)       

open import Data.Empty     public
open import Data.Product   public
  using (_×_; _,_; proj₁; proj₂)
open import Data.Sum       public
  using (_⊎_; inj₁; inj₂)
  renaming ([_,_] to join)

open import Data.Unit      public
  using (⊤; tt)
open import Data.Bool      public
  using (Bool; true; false; if_then_else_; _∨_; _∧_)
open import Data.Nat       public
  hiding (_≟_; _⊔_)
open import Data.Nat.Show  public
open import Data.Fin       public
  using (Fin; fromℕ; fromℕ<; fromℕ<″)
open import Data.String    public
  using (String)
  renaming (_++_ to _<>_)
open import Data.Maybe     public
  using (Maybe; maybe′; just; nothing; fromMaybe; _<∣>_; when; boolToMaybe)
open import Data.List      public
  using (List; []; _∷_; _++_; length; break; [_]; concat; zip; zipWith; foldr; lookup; reverse)

open import Relation.Nullary public
  using (Dec; does; no; yes)

open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; cong; cong₂)

open import Category.Monad public

open import Reflection     public
  hiding (_≟_)
open import Reflection.Argument     public
  using (unArg)

open import Agda.Primitive          public
open import Agda.Builtin.Reflection public
  using (declareData; defineData)
  -- declareData is newly added
  
-- Type classes
open import Prelude.Functor  public
open import Prelude.Equality public
