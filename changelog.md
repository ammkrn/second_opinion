
## 0.1.0 -> 0.1.1

+ Switch to bump allocator for both Mmb and Mmz
+ Extract `MmbItem::Var` and `MmbItem::App` to a new enum `MmbExpr`
+ Change MmbItem to be direct, based on references into the bump allocator
+ Remove Mmb formatters since they can now be formatted directly.
+ Change MmbItem sequence type to BumpVec instead of a linked list.
+ Remove MmbMem since the persistent mmb state is now just `Outline` and `Bump`
+ Consistently check for and reject duplicate precedence declarations
+ Remove a bunch of hard `unreachable!()` invocations.
