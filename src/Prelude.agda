{-# OPTIONS --without-K --safe #-}
module Prelude where 

-- Built-in modules 
open import Agda.Builtin.Unit             public
  
-- Basic   
open import Prelude.Level                 public
open import Prelude.Function              public
open import Prelude.Relation              public

-- Type classes (without instances unless builtin)
open import Prelude.Show                  public
open import Prelude.Eq                    public
open import Prelude.Coercion              public
open import Prelude.Functor               public
open import Prelude.Applicative           public
open import Prelude.Monad                 public
open import Prelude.Alternative           public

-- Data Types
open import Prelude.Empty                 public
open import Prelude.String                public
open import Prelude.Bool                  public
open import Prelude.Nat                   public
open import Prelude.Maybe                 public
open import Prelude.List                  public
open import Prelude.Sigma                 public
open import Prelude.Sum                   public
