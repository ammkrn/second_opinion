
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

## 0.1.3 -> 2.0

+ Remove native mmb parsing facilities in favor of the ones in mm0-rs/components/mmb_parser; the version of `second_opinion` that relies on native implementations will remain available in the `native` fork.
+ Remove ConvRef, change conv implementation
+ The main verificaiton only returns one (the first) error instead of accumulating any and all errors. Since there's a backtrace provided, I didn't find the multiple error reporting to be helpful.
+ The FileData struct is now a RawFileData struct that owns the underlying data, and FileView is passed around since we need to show that the data backing the parsed MmbFile lives as long as the verification is going on.
+ Break out MmzImporter so we can discard the garbage collected while traversing the mmz import graph.
+ Most methods and structs now use the native SortId, TermId, ThmId instead of u8/u32s.
+ The native Mods was replaced with the upstream Modifiers.
+ Removed most of the outstanding unwraps which were in the `fs` module. They now return a proper error.
+ Fix bug in bound variable counter
