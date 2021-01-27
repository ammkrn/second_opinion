
## What is this?
A verifier for [Metamath Zero](https://github.com/digama0/mm0) proof files.

## short-term TODOs
- Improve interface
- Work on inline docs
- Better errors/error-handling
- Redo the pos/idx counters for variables in the mmz parser so that they ignore dummy variables instead of compensating for them.
- I think the parser should deal with an &str source instead of &[u8] for mmz files since you already know it has to be ascii. This would make some stuff nicer and let us get rid of `Str`
- More tests. It would be cool to do some property-based testing, but it's not always easy to identify meaningful invariants.


## Use

Invoke the binary, passing a relative path (like `./p_eq_np/proof.mmb`) and an optional relative path to the mm0 file that sits at the top of the import graph. If no mm0 file is passed explicitly, the verifier will look for one in the same directory as the passed mmb file. You can optionally specify the number of threads to use with the flag `-t <number>` or `--threads <number>`.

Just to clarify w.r.t. the imports:
If we have an mm0 project `p_eq_np` in a directory which has some mm1 files, mm0 files, and some other stuff, where `a.mm1` is the top-level file, importing `b` and `c`, compiling `a.mm1` will produce a single mmb file.
```
├── my_machine/p_eq_np
    ├── a.mm0
    ├── b.mm0
    ├── c.mm0
    ├── a.mm1
    ├── b.mm1
    ├── c.mm1
    ├── README.md
    ├── ... other files in this directory ...
```

To run this verifier on your project using 4 threads, you would invoke
`./second_opinion -t 4 ./a.mmb` or `./second_opinion -t 4 ./a.mmb ./a.mm0`.

## The big picture

This verifier requires two kinds of files for verification. 
1. The mm0 file.
The mm0 file is where metamath zero users keep a specification describing the contents of an mm1 file. You can think of this as a blueprint, or something like a header file for your mm1 file. The presence of an mm0 file in addition to the mm1 file is desirable because it allows users to ensure that the data passing through the verifier actually represents what you expect it to (that what's being proved is what you intended).

1. The mmb file.
The mmb file is a binary file (a big sequence of bytes) produced by a compiler for mm1. The mmb file contains information about each declaration in the mm1 file as well as the proof and unification steps that need to be checked by the verifier.

Declarations in an mm1 file (sorts, terms, assertions) can be either local or non-local (public). Local declarations are those which exist only in the mm1 file, like auxiliary theorems (lemmas, but mm1 has no lemma keyword) and helper definitions. These appear in the mmb file since they need to be verified, but they do not appear in the mm0 file. The declarations that are in both the mm1 and mm0 file are public/non-local. Sorts, terms, and axioms are always public/non-local. As such, they go through an additional check in the mmz parser, which demands that the item parsed from the mm0 file unifies under the instructions given in the mmb file.

The flowchart for the verification process is as follows:

0. File system stuff; open the mmb file, find the imports and open the necessary mm0 files.

1. Parse the header of the mmb file, which makes sure you actually have an mmb file (by checking the [magic number](https://en.wikipedia.org/wiki/File_format#Magic_number)). The header also contains some basic information, like the number of sorts/terms/theorems, as well as pointers to the beginning of important streams. 

2. Parse the mmb index, which is as the name implies; a store of auxiliary information (like declaration names)

3. Guided by the header, iterate over the declarations in the mmb file (sorts, terms, assertions) and get their proofs.

4. For each declaration, if it's a sort, just add it making sure it doesn't conflict or overflow. If it's a termdef or assertion, execute `run_proof` and `run_unify` using the ProofIter and UnifyIter respectively.

5. If the declaration is public (exists in the mm0 file), parse that declaration from the mm0 file, check it, and add it to the environment.

6. While parsing the mm0 file's contents, process any notation declarations, coercions, or input/output (currently unhandled) statements.

Proof streams and unification streams are sequences of instructions given to the verifier by the compiled mmb file. 
The verifier (which executes proof/unification streams) is comprised of stacks and heaps, which are just vectors from which we pop/push/read elements.

## Imports
This verifier is currently capable of handling import diamonds, but import cycles are rejected with a hard error. We require that the mm0 file passed to the verifier be the top element in the import heirarchy. For example, `a.mm0` in the following import graph:
```
      a
     /  \
    b   c
  / \   / \
 d  e  f   g
```


## Types
Types are represented as 64 bit integers and manipulated with bit-masks and bitwise operations. This verifier puts a minimal layer of abstraction over it, but without explanation it's still fairly opaque. By `type`, we mean something to the right of the colon in a binder or return type; the information it can/may contain is a sort, whether the item is bound or free, and either the item's dependencies, or an indication of which bound variable it is (1 - 55). The high bit is always in indication of bound/not bound. It's 0 if the variable is free, and 1 if bound. The high byte's remaining 7 bits show the sort numer (0 - 127). The remaining/lower 7 bytes will either have a single `1` bit showing which bound variable it is, or it will have between 0 and 56 `1` bits which show the variable's dependencies.

The "last" bound variable index (the 56th bit) is reserved for a future extension in which a hot 56th bit will indicate that there are additional bound variables in another location. 

For bound variables that have dummy identifiers (like {.x : nat}), the bound variable is accounted for during the actual proof-checking process, and their bit comes "after" (higher in the bitfield) the other bound variables. Specifically, they're introduced as needed by `mmb::proof::proof_dummy`.

In the `utils` module, `Arg` is an alias for `Type`.

A few examples:

For a variable which is:
1. An element of the 2nd sort declared
2. Bound
3. The 5th bound variable in the declaration

```
-- is bound                                                       --- 5th bound variable
|                                                                 |
10000010_00000000_00000000_00000000_00000000_00000000_00000000_00010000
      |__ sort 2
```


For a variable which is:
1. An element of the 7th sort declared
2. Not bound
3. Depends on variables 3 and 16

```
-- not bound                                            dependencies (3 and 16)
|                                                     |             |
00000111_00000000_00000000_00000000_00000000_00000000_10000000_00000100
     |_| sort 7

```

