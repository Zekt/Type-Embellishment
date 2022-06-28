{-# OPTIONS --rewriting --guardedness --sized-types #-}

{-
  To typecheck this file in Emacs with Agda mode, the current directory needs
  to be part of the include path: type the following

  ```
  M-x customize-option RET agda2-program-args RET
  ```

  and add a new argument by inserting a new string

  ```
  -i.
  ```

  Then, apply the setting.
-}

module README where

------------------------------------------------------------------------------
-- Examples using macro
------------------------------------------------------------------------------

-- Datatypes and functions are generated through tactics using
-- `unquoteDecl` and `unquoteDecl data`.

-- * Running examples in section 2, 3 and 4.
import Examples.WithMacros.Acc

-- * Other examples
import Examples.WithMacros.W
import Examples.WithMacros.Nat
import Examples.WithMacros.List
import Examples.WithMacros.BST
import Examples.WithMacros.STLC

------------------------------------------------------------------------------
-- Main framework
------------------------------------------------------------------------------

-- * Section 2.1, only used to compare with the classic approach of DGP
-- but not used in our framework.
import Generics.Description.FixedPoint

-- * Section 3
import Generics.Description
import Generics.Telescope

-- * Section 4
import Generics.Algebra               
import Generics.Recursion

-- * Section 5
import Generics.Reflection
import Generics.Reflection.Telescope
import Generics.Reflection.Datatype
import Generics.Reflection.Connection
import Generics.Reflection.Uncurry
import Generics.Reflection.Recursion

-- * Section 6
import Generics.RecursionScheme
import Generics.Ornament
import Generics.SimpleContainer

------------------------------------------------------------------------------
-- Utilties
------------------------------------------------------------------------------

-- * A tactic for printing the definition of a given name.

import Utils.Reflection.Print

-- To inspect the definition of a datatype or a function called `x`, invoke
--
-- `print D` or `print F`
--
-- by pressing `Ctrl+C Ctrl+N` in agda mode, the definitions will be printed
-- to the debug buffer (*).

-- (*) To open the debug buffer, see the following instructions
-- according to your editor:

-- (1) For Emacs: select the *Agda Debug* buffer.

-- (2) For VS Code: execute Agda: Open Debug Buffer in the Command Palette.

------------------------------------------------------------------------------
-- A minimal prelude
------------------------------------------------------------------------------

import Prelude

------------------------------------------------------------------------------
-- Everything (else)
------------------------------------------------------------------------------

import Everything
import EverythingSafe
