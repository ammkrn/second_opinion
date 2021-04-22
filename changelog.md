
## 0.1.0 -> 0.1.1

+ Switch to bump allocator for both Mmb and Mmz
+ Extract `MmbItem::Var` and `MmbItem::App` to a new enum `MmbExpr`
+ Change MmbItem to be direct, based on references into the bump allocator
+ Remove Mmb formatters since they can now be formatted directly.
+ Change MmbItem sequence type to BumpVec instead of a linked list.
+ Remove MmbMem since the persistent mmb state is now just `Outline` and `Bump`
+ Consistently check for and reject duplicate precedence declarations
+ Remove a bunch of hard `unreachable!()` invocations.

## 0.1.1 -> 0.1.2

+ Use bump allocator for MmzItem and MathStr. 
+ Remove mmz string sharing (remove indexmap and rustchash dependencies)
+ Change error reporting in main since mmz_mem is no longer `Send`.
+ style changes in math parser

## 0.1.2 -> 0.1.3

+ Add `occupied_precs` map for math-parser disambiguation.
+ refactor lhs handling in math-parser

## 0.1.3 -> 0.1.4

+ Remove ConvRef
+ Update Ref/Update
+ Fix bug in function taking next bound variable

