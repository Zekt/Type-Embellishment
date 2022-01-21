# Type Embellishment

This repo contains
* A representation for generic programs and generic functions,
* metaprograms for traslation between generic and native datatypes/functions,
* relations between generic and native definitions, and
* examples.

What has been established on generic definitions (e.g. Ornamentation) can be reified.
Ideally, users can benefit from generic libraries while work in familiar and comfortable world of native definitions, without interacting with generic programs.

For most generic programs and their native counterparts there are translation relations to be written,
metaprograms automates the process, making native programmers and generic programmers live in harmony.

Here's a list of definitions and their intended ways of generation: 

|                  |   Object Level    | define (unquoteDecl) |  gen (macro)  |
|------------------|-------------------|----------------------|---------------|
| Native Data      | -                 | o (defineByDataD)    | x             |
| DataD            | -                 | x                    | o (genDataD)  |
| DataC            | -                 | x                    | o (genDataC)  |
| Data Wrapper     | -                 | x                    | o (genDataT)  |
| Native Fold/Ind  | -                 | o (defineFold/Ind)   | x             |
| FoldP/IndP       | o (fold-operator) | x                    | x             |
| FoldC/IndC       | -                 | x                    | o (genFoldC)  |
| Fold/Ind Wrapper | -                 | x                    | o (genFoldGT) |
