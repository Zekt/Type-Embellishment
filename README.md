# Datatype-Generic Programming Meets Elaborator Reflection

## Introduction

This repo contains
* representations for inductive families and generic programs,
* metaprograms and macros for traslation between generic and native datatypes/functions,
* connections between generic and native definitions, and
* examples.

There are also highlighted and clickable HTML documents for traversing the modules in the `html` directory. The start page is `Everything.html`.

## Requirement

* 14 Gigabytes of memory or above.
* The development version of Agda 2.6.3 ([commit 1b44372](https://github.com/agda/agda/commit/1b44372081e5b21b1a368d0e63cc09a53c48d20b))
  extended with an experimental syntax `unquoteDecl data` by applying
  * Agda-unquoteDecl-data.diff 

## Patch & compile Agda
1. `git clone https://github.com/agda/agda.git`
2. `cd agda && git checkout 1b44372`
3. `git apply ../*.diff`
4. `make install-bin`
5. Check the Agda binary version by `agda-2.6.3 -V`, which should output `Agda version 2.6.3-8f8b1f9-dirty`

## Check all modules
Type `make AGDA_BIN=agda-2.6.3` to check all modules in the `src` directory with the patched Agda binary.

## Details

	src
	├── Examples
	│   ├── WithMacros
    │   │   ├── Acc.agda ----------- Running examples in section 2, 3 and 4.
	│   │   └── ...
	│   └── WithoutMacros
	│       └── ...
	├── Generics
	│   ├── Algebra.agda ----------- Section 4.2 (Figure 6).
	│   ├── Description
	│   │   └── FixedPoint.agda ---- Section 2.1.
	│   ├── Description.agda ------- Section 3 (Figure 1, 2, 3 and 4).
	│   ├── Ornament --------------- Section 6.2.
	│   │   └── ...
	│   ├── Recursion.agda --------- Section 4.1 and 4.2 (Figure 5, 6 and 7).
	│   ├── RecursionScheme.agda --- Section 6.1.
	│   ├── Reflection ------------- Section 5.
	│   │   ├── Connection.agda ---- Section 5.3.
	│   │   ├── Datatype.agda ------ Section 5.2.
	│   │   ├── Recursion.agda ----- Section 5.4.
	│   │   ├── Telescope.agda ----- Section 5.2.
	│   │   └── Uncurry.agda ------- Section 5.3.
	│   ├── SimpleContainer -------- Section 6.3.
	│   │   └── ...
	│   └── Telescope.agda --------- Section 3.2.
	└── Utils
	    ├── Reflection
	    │   ├── Print.agda --------- (*)
	    │   ├── Tactic.agda -------- Section 5.2.
	    │   └── ...
	    └── ...

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
