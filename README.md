# Datatype-Generic Programming Meets Elaborator Reflection

## Introduction

This repo contains
* representations for inductive families and generic programs,
* metaprograms and macros for translation between generic and native datatypes/functions,
* connections between generic and native definitions, and
* examples.

There are also highlighted and clickable HTML documents for traversing the modules in the `html` directory. The start page is `Everything.html`.

## Requirement

* 6GB of memory or above.
* The development version of Agda 2.6.3 ([commit 1b44372](https://github.com/agda/agda/commit/1b44372081e5b21b1a368d0e63cc09a53c48d20b))
  with the patch
  * `Agda-unquoteDecl-data.diff` to extended Agda with an experimental syntax `unquoteDecl data`

## Patch & compile Agda
1. `git clone https://github.com/agda/agda.git`
2. `cd agda && git checkout 1b44372`
3. `git apply ../Agda-unquoteDecl-data.diff`
4. `make install-bin`
5. Check the Agda binary version by `agda-2.6.3 -V`, which should output `Agda version 2.6.3-1b44372-dirty`

## Check all modules
Type `make AGDA_BIN=agda-2.6.3` to check all modules in the `src` directory with the patched Agda binary.

## Details

	src
	├── Examples
	│   ├── WithMacros
    │   │   ├── Acc.agda ----------- Running examples in section 2, 3 and 4.
    │   │   ├── List.agda ---------- Examples in section 6.2 and 6.3.
    │   │   ├── BST.agda ----------- Examples in section 6.3.
	│   │   └── ...
	│   └── WithoutMacros
	│       └── ...
	├── Generics
	│   ├── Algebra.agda ----------- Section 2.2 (^1)
	│   ├── Description
	│   │   └── FixedPoint.agda ---- Section 2.1.
	│   ├── Description.agda ------- Section 3, 5.2, 5.3, Figure 1, 2 and 9(^2).
	│   ├── Ornament --------------- Section 6.2.
	│   │   ├── Algebraic.agda ----- Section 6.2(^3).
	│   │   └── ...
	│   ├── Recursion.agda --------- Section 3.2, 4.3, Figure 6 and 7(^2).
	│   ├── RecursionScheme.agda --- Section 6.1.
	│   ├── Reflection ------------- Section 4.
	│   │   ├── Connection.agda
	│   │   ├── Datatype.agda
	│   │   ├── Recursion.agda ----- Section 4.3 and Figure 8(^2).
	│   │   ├── Telescope.agda ----- Section 4.2.
	│   │   └── Uncurry.agda ------- Section 4.3.
	│   ├── SimpleContainer -------- Section 6.3 and Figure 11.
	│   │   └── ...
	│   └── Telescope.agda --------- Section 3.1, 5.1, Figure 3, 4, 5 and 10(^2).
	└── Utils
	    ├── Reflection
	    │   ├── Print.agda --------- (*)
	    │   ├── Tactic.agda -------- Section 4.2.
	    │   └── ...
	    └── ...

(^1): `Alg` is renamed to `Algᶜˢ` in the files.  
(^2): Definitions in the main text before section 4 and those in figure 1 to 8 are not universe polymorphic, thus are different from their corresponding definitions in the files. See section 5 for their exact definitions.  
(^3): Instead of `AlgO` and `AlgD` in section 3.2, an `AlgOD` that combines both is defined.  

(\*) To inspect the definition of a datatype `D` or a function `F`, import this module and normalise `print D` or `print F` (Ctrl+C Ctrl+N in agda mode), the definitions will be printed to the debug buffer(\*\*).  
(\*\*) To open the debug buffer, select the `*Agda Debug*` buffer in Emacs, or execute `Agda: Open Debug Buffer` in the Command Palette of Visual Studio Code (see [agda-mode](https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode)).

Here's a list of definitions and their intended ways of generation: 

|                  |   Expression                    | Declaration            |  Macro      |
|------------------|---------------------------------|------------------------|-------------|
| Data type        | N/A                             | `defineByDataD`        | N/A         |
| DataD            |                                 |                        | `genDataD`  |
| DataC            |                                 |                        | `genDataC`  |
| Data type wrapper|                                 |                        | `genDataT`  |
| Native Fold/Ind  |                                 |`defineFold` `defineInd`|             |
| FoldP/IndP       | `fold-operator` `ind-operator`  | N/A                    |  N/A        |
| FoldC/IndC       |                                 |                        | `genFoldC`  |
| Fold/Ind Wrapper |                                 |                        | `genFoldGT` |
