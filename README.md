# Type Embellishment

This repo contains
* a representation for inductive families (`DataD`), generic function (`FoldP`), and generic programs (`IndP`),
* metaprograms and macros for traslation between generic and native datatypes/functions,
* connections between generic and native definitions, and
* examples.

What has been established on generic definitions (e.g. ornamentation) can be reified.
Users benefit from generic libraries while work in the familiar and comfortable environment of conventional definitions,
without (object-level) conversions between generic datatypes and generic programs.

For most generic programs and their native counterparts there are translation relations to be written,
metaprograms automates the process, making native programmers and generic programmers live in harmony.

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
