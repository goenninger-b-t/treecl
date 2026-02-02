# TreeCL Knowledge Base (from references PDFs)

This file captures facts and implementation-relevant notes extracted from the PDFs in
`references/`. It is meant to be a stable, local summary for TreeCL development.

--------------------------------------------------------------------------------
Source: tree_book.pdf (Barry Jay, "Tree Calculus")
--------------------------------------------------------------------------------
- Syntax (BNF): M, N ::= 4 | M N. Application is left-associative; each "4" is a node,
  and each application M N adds an edge from the root of M to the root of N.
- Natural tree classes:
  - Leaf: a node with no branches (4).
  - Stem: a node with one branch (4 x).
  - Fork: a node with two branches (4 x y), with ordered left/right branches.
- Programs/values are binary trees: leaves, stems, and forks whose branches are also
  binary trees. Any tree containing a node with three or more branches is a
  computation that must be evaluated. A term 4 M N P triggers evaluation, so 4 is a
  ternary operator that fires when it has three arguments.
- Core evaluation rules (K, S, F), driven by the structure of the first argument:
  - 4 4 y z = y
  - 4 (4 x) y z = y z (x z)
  - 4 (4 w x) y z = z w x
  Notes: K deletes the third argument, S duplicates the third argument, and F
  decomposes the first argument to expose its branches.
- Basic combinators in tree calculus:
  - K = 4 4
  - I = 4 (4 4) (4 4)
  - D = 4 (4 4) (4 4 4)
  - d{x} is shorthand for 4 (4 x) in derivations.
- Natural numbers (Chapter 3.7):
  - Represent n as K^n 4 (zero is 4; successor is K).
  - isZero = d{K 4 I}(d{K K}4).
  - predecessor = d{K 2 I}(d{K4}4).
- Fundamental queries exist for structural inspection:
  - isLeaf, isStem, isFork can be defined using a generalized "query" that
    distinguishes leaf/stem/fork.
  - query {is0,is1,is2} = d{K is1}(d{K 2 I}(d{K 5 is2}(d{K 3 is0}4))).
  - A "triage" combinator packages these tests to select among three functions
    based on whether its argument is a leaf, stem, or fork. This is used by
    programs like size and equality.
- Alternate boolean-style queries (Chapter 5):
  - isStem2 = lambda* z. 4 z 4 (K 2 4)
    - Maps leaves and forks to a leaf (false), and a stem 4x to a fork
      4 (K 2 4) (x (K 2 4)).
  - isFork2 = lambda* z. 4 z (K K) (K (K 4))
    - Maps forks to 4 and maps leaves/stems to forks.
- Triage combinator (Chapter 5):
  - triage_comb = lambda* f0. lambda* f1. lambda* f2. lambda* z.
    isStem2 z (4 z f0 f2) (4 (z 4) 4 (lambda* x. K (f1 x)))
  - Semantics: triage{f0,f1,f2} 4 = f0; triage{f0,f1,f2} (4 x) = f1 x;
    triage{f0,f1,f2} (4 x y) = f2 x y.
- Evaluation strategies are defined within tree calculus:
  - Branch-first: evaluate branches before evaluating the root.
  - Root evaluation: evaluate only enough to determine leaf/stem/fork (factorable
    forms), potentially leaving branches unevaluated (quoted).
  - Root-and-branch: perform root evaluation, then recursively evaluate branches.
  These strategies are used to build self-evaluators.

--------------------------------------------------------------------------------
Source: Graham, Paul - ANSI Common Lisp.pdf
--------------------------------------------------------------------------------
- Evaluation rule for function calls:
  - Evaluate arguments left-to-right.
  - Apply the operator (function) to the evaluated arguments.
- quote is a special operator: it returns its argument verbatim (no evaluation).
  The reader abbreviation ' is equivalent to quote.
- if is a special operator: evaluates the test, then evaluates only one branch.
  The else branch is optional and defaults to nil.
- and/or are macros: they short-circuit, evaluating only as many arguments as needed.
- nil is both the empty list and false. t is the default truth value; anything other
  than nil is treated as true. The functions null and not both test for nil.
- Closures:
  - A closure is a function plus an environment.
  - Closures are created when a function refers to free lexical variables; the
    variables persist as long as the closure does.

--------------------------------------------------------------------------------
Source: Art of Metaobject Protocol.txt
--------------------------------------------------------------------------------
- OCR text is available (see `Art of Metaobject Protocol.txt`). The index enumerates
  the full MOP surface area: class/generic/method metaobject accessors, class
  finalization and CPL computation, slot definition protocols (direct/effective),
  dependents, EQL specializers, funcallable instances, and GF invocation protocols
  (compute-discriminating-function/effective-method, etc.).

--------------------------------------------------------------------------------
MOP implementation status (TreeCL)
--------------------------------------------------------------------------------
- Current MOP is a mini-MOP. It supports basic classes, generics, methods, and a subset of method combination.
- Added class metaobject slots in `standard-class` with slot-visible metadata: name, direct-superclasses/subclasses, direct/effective slots, CPL, finalized-p, instance-size.
- Class objects now map to metaobject instances for slot access; unbound slot values are tracked explicitly.
- Exported `standard-class` slot names from `COMMON-LISP` so `CL-USER` symbols like
  `name`/`direct-superclasses` resolve to the same slot names.
- Added metaobject classes for generics, methods, and slot definitions
  (`standard-generic-function`, `standard-method`, `standard-(direct|effective)-slot-definition`)
  with instance-backed slot access.
- Implemented class creation protocol pieces: `ensure-class-using-class` wrapper, `validate-superclass`
  default method, `finalize-inheritance` recomputation, `reinitialize-instance`, `change-class`,
  class default initargs, and slot-names-aware `shared-initialize` (defaults applied when slot-names is non-nil).
- Implemented a setf expansion hook for accessors using a `slot-accessor` property to route `(setf (reader obj) val)` to `set-slot-value`.
- Equality for CLOS objects (class/instance/generic/method/slot-definition) compares by id rather than node identity.
- Added `slot-missing` and `slot-unbound` generics with default error methods; slot access primitives now invoke them.
- Added `make-direct-slot-definition`/`make-effective-slot-definition` via sys primitives backed by standalone slot-definition storage.
- `shared-initialize` now honors `initfunction` (evaluated to a function when needed) and enforces slot types for initargs/defaults.
- Fixed APPLY/FUNCALL on closures by driving the TCO evaluator until the continuation stack completes (use `step()` loop, not just `ExecutionMode::Return`).
- Generic function invocation now applies cached discriminating functions (from `compute-discriminating-function`) instead of always raw dispatch.
- Primitives that call `apply_values` now preserve process state (program/mode/continuation stack/pending redex/next-method state) to avoid clobbering ongoing evaluation.
- Added EQL specializer support: `eql-specializer` class, `intern-eql-specializer`, `eql-specializer-object`, EQL-aware method applicability/specificity, and dispatch that ignores caching when EQL specializers are present.
- Added dependents protocol support: `add-dependent`, `remove-dependent`, `map-dependents`, and `update-dependent` generics backed by MOP storage, with update notifications on class/generic redefinition and method addition.
- Added funcallable instances: `funcallable-standard-class`/`funcallable-standard-object`, `set-funcallable-instance-function` (generic + funcallable instances), and `funcallable-standard-instance-access`.
- Open tasks tracked in `TASKS.md` cover extra introspection and accessor completeness.
