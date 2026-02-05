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
- Implemented canonical `(setf <reader>)` generic functions for `:accessor` slots and setf function-name handling, so `(setf (reader obj) val)` routes through the setf generic (no slot-accessor property needed).
- The `function` special operator now resolves `(setf <symbol>)` names to setf generics/functions, so setf expansions invoke the proper generic (including :before/:after methods).
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
- Added introspection extras: `class-direct-methods`, `class-direct-generic-functions`, `specializer-direct-methods`, and `specializer-direct-generic-functions`.
- Accessor/setf completeness is now covered by Task 10 in `TASKS.md` (done).
- Process-level caching: NIL/T/UNBOUND nodes are cached per process arena (`make_nil`, `make_t`, `make_unbound`) to reduce allocations and stabilize identity for NIL/T; instance allocation reuses the cached UNBOUND node.

--------------------------------------------------------------------------------
ANSI Common Lisp compliance status (TreeCL, Feb 4 2026)
--------------------------------------------------------------------------------
- Status summary: TreeCL is an experimental CL with a working evaluator, basic reader, minimal standard library, and a mostly-complete MOP, but it is far from full ANSI compliance. Many ANSI test categories are missing or partially stubbed.
- Special forms and evaluator: core forms like `quote`, `if`, `progn`, `setq`, `let`, `lambda`, `function`, `block`, `return-from`, `tagbody`, `go`, `catch`, `throw`, `unwind-protect`, `defmacro`, multiple values (`values`, `values-list`, `multiple-value-bind`, `multiple-value-call`, `multiple-value-prog1`, `multiple-value-list`, `nth-value`), `flet`, `labels`, `macrolet`, `symbol-macrolet`, `load-time-value`, `progv` exist, but some ANSI forms are missing or incomplete, notably `eval-when`, `the`, and full declaration handling (`locally`/`declare`) in `src/eval.rs`.
- Reader/readtable: `src/reader.rs` supports lists, strings, quote/quasiquote/unquote, line and block comments, `#'`, `#\` character literals (stored as integers), `#(` vectors, `#:` gensyms, `#x/#o/#b` radix ints (including ratios parsed to float), `#P` pathnames (pass-through), `#+/-` feature checks using `*FEATURES*`, `#.` read-time eval (gated by `*read-eval*`), `#n=`/`#n#` labels, `#nR` radix integers/ratios (ratios coerced to float), plus `#*` and `#nA` parsing (currently mapped to nested vectors via `ArrayStore`). Numeric tokens now parse integers, ratios, and floats in base 10 (ratios still coerced to float). Readtables support case modes, `*readtable*`, and macro/dispatch tables (including numeric arguments to dispatch macros). Missing or incomplete: `#S` and `#C` still rely on structures/complex numbers (not yet implemented), full `#R` for floats/complex and exact rationals, float subtype integration (`*read-default-float-format*`), and proper character type integration.
- Packages/symbols: `src/symbol.rs` implements basic packages (COMMON-LISP, KEYWORD, CL-USER), intern, export, find-package, and in-package. Missing: `defpackage`, `find-symbol` status, import/export/shadowing/shadowing-import/unintern/use-package/unuse-package, package nicknames management, with-package-iterator, and most package accessors (use-list/used-by-list/shadowing-symbols).
- Numbers: numeric tower is limited to integers, bignums, and f64 floats (`OpaqueValue::Integer`, `BigInt`, `Float`). Missing: ratios, complexes, float subtypes, and most numeric functions (`floor`, `ceiling`, `round`, `truncate`, `rational`, `numerator`, `denominator`, `phase`, etc.).
- Characters/strings: characters are not a distinct type (reader maps `#\` to integer). String functionality is minimal; many ANSI string functions and character predicates are missing.
- Arrays/sequences: arrays are only simple vectors in `src/arrays.rs`, with `make-array/aref/set-aref` support for one-dimensional vectors. Missing: multi-dimensional arrays, adjustable arrays, fill pointers, displaced arrays, bit-vectors, and full sequence functions (`elt`, `subseq`, `map`, `reduce`, `position`, `remove`, `sort`, etc.).
- Hash tables: `src/hashtables.rs` implements a linear-scan hash table with tests `eq/eql/equal/equalp`, but lacks hashing, rehashing controls, and standard API surface (maphash, clrhash, hash-table-xxx accessors, sxhash).
- Streams/files/pathnames: `src/streams.rs` covers basic standard streams plus string/file/broadcast/two-way/echo/synonym scaffolding; `read-char`/`unread-char`/`read-line` exist but only for string streams, and `make-two-way-stream`/`make-broadcast-stream` are minimal. Missing ANSI stream functions include `open`, `peek-char`, `read-byte`, `write-byte`, `finish-output`, `force-output`, `clear-output`, `file-position`, `file-length`, and full stream predicates/behavior. Pathname functions in `src/primitives.rs` remain stubs (`make-pathname`, `merge-pathnames`, `pathname-type`, `truename`, `directory`, `compile-file-pathname`).
- Conditions: `src/conditions.rs` provides basic handler/restart stacks and simple error types, but `define-condition`, `signal`, `warn`, `handler-case`, `restart-case`, `invoke-restart`, and correct condition class integration with CLOS are missing or incomplete.
- Compiler/load: `load` in `src/primitives.rs` reads and evals forms from a file; there is no ANSI `compile-file` pipeline. `macroexpand-1` now returns multiple values, but `macroexpand` and `eval-when` semantics are still missing.
- Types/structures: `typep`, `subtypep`, `type-of`, `deftype`, and `defstruct` are missing. Type declarations and `the` are not enforced.
- Printer: `format` exists but is limited; `print`/`prin1`/`princ` support is minimal, and `*print-*` variables and pretty printer are not implemented.
- CLOS: MOP is strong, but ANSI class/type integration, built-in classes, full method combination, and CLOS-related type predicates remain incomplete.
- ANSI tests: the suite lives in `tests/ansi-test`. Full compliance will require closing the gaps above, then running category-by-category tests.
- ASDF: `src/asdf.lisp` is now present, but loading it still requires full ANSI reader behavior, package system, pathnames/files/streams, `eval-when`/`load-time-value`, and condition handling.

--------------------------------------------------------------------------------
Progress update (Feb 4 2026)
--------------------------------------------------------------------------------
- Added `src/asdf.lisp` (vendor drop-in) for ASDF bootstrap work.
- Multiple values now supported (`values`, `values-list`, `multiple-value-bind`, `multiple-value-call`, `multiple-value-prog1`, `multiple-value-list`, `nth-value`); `macroexpand-1` returns multiple values.
- Reader/readtable upgrades: readtable case modes, `*readtable*`/`*read-base*`/`*read-eval*`/`*read-suppress*`/`*features*` defaults, readtable macro/dispatch tables, `read`/`read-preserving-whitespace`/`read-from-string`/`read-delimited-list`, dispatch macros `#.`/`#| |#`/`#n=`/`#n#`/`#nR` (integers/ratios) with numeric dispatch arguments, plus `#*` bit-vectors and `#nA` arrays (nested vectors). Numeric token parsing now handles ratios/floats in base 10 (ratios coerced to float) and dot tokens require escapes. `#C`/`#S` now parse and attempt construction via `COMPLEX` or `MAKE-<STRUCT>` when available. Feature expressions now consult `*features*`.
- Streams: `read-char`/`unread-char`/`read-line` implemented for string streams; `make-two-way-stream`/`make-broadcast-stream` exist but are minimal.
- Remaining gaps for ANSI reader compliance: `#S`/`#A`/`#*`/`#C`, full numeric token grammar (ratios/floats/exponents), and full stream integration for reader entry points.

--------------------------------------------------------------------------------
Progress update (Feb 5 2026)
--------------------------------------------------------------------------------
- Added an `in-package` macro in `src/init_new.lisp` so the designator is not evaluated (ANSI behavior); it calls the `IN-PACKAGE` primitive via `funcall`.
- Reader harness `tests/ansi-test/reader/load.lsp` now emits progress prints. Running it with a 300s timeout fails after `compile-and-load` with `IN-PACKAGE: unknown package` because `CL-TEST` is not created yet. This confirms Task 2 package system work is required (make-package, use-package, shadow/import/export, etc.) before running the reader suite standalone.
- Regression: `cargo test -q` passes.

Progress update (Feb 5 2026, Task 2)
--------------------------------------------------------------------------------
- Package system expanded in `src/symbol.rs`: packages now track use-lists, used-by lists, shadowing symbols, deletion state, and documentation; new helpers support package creation, deletion, renaming, shadowing, and symbol lookup status (:internal/:external/:inherited).
- New package/symbol primitives added in `src/primitives.rs` for `make-package`, `delete-package`, `rename-package`, `packagep`, `find-symbol`, `find-all-symbols`, `export`/`unexport`, `import`, `shadow`/`shadowing-import`, `unintern`, `use-package`/`unuse-package`, package accessors, `gentemp`, and a `sys-package-iterator-entries` helper to drive `with-package-iterator`.
- `gensym` now supports integer arguments and big counters (separate from `gentemp`), `copy-symbol` supports optional plist/value/function copying, and `boundp` treats `NIL`, `T`, and keywords as bound.
- `*package*`, `*gensym-counter*`, and `*gentemp-counter*` are initialized in `Process::new`; `setq`/`defvar`/`defparameter`/`let` update `*package*` and treat `*...*` variables as special (dynamic) bindings.
- Reader `pkg:symbol` now requires external symbols; `pkg::symbol` continues to intern internal symbols. String designators now accept character vectors with fill pointers; `make-array` preserves character vectors with fill pointers/displacement rather than collapsing to raw strings.
- `src/init_new.lisp` now defines `defpackage`, `with-package-iterator`, `do-symbols`, `do-external-symbols`, and `do-all-symbols` macros to support ANSI package tests and ASDF bootstrapping.

Progress update (Feb 5 2026, ANSI package/symbol tests attempt)
--------------------------------------------------------------------------------
- Attempted to run `tests/ansi-test/packages` and `tests/ansi-test/symbols` via a minimal harness (`cargo run --bin treecl -- /tmp/ansi_packages_symbols.lsp`).
- First run failed at read time because the harness referenced `regression-test:do-tests`; TreeCL reads the entire file before evaluation, so package-prefixed symbols must already exist at read time (workaround: use `(intern "DO-TESTS" "REGRESSION-TEST")` or avoid package prefixes in the harness file).
- After adjusting the harness to avoid package-prefixed symbols, load failed while reading `tests/ansi-test/rt-package.lsp` with `LOAD: read error: Unexpected character: ')'`. This indicates a reader incompatibility with the RT harness file before package/symbol tests can run.
- Even if RT loads, many package/symbol tests (and aux files) rely on full ANSI `loop` syntax and condition system (`handler-case`/`signals-error`), which are not implemented yet; these are expected blockers for running the suite end-to-end.

Progress update (Feb 5 2026, reader conditionals and comments)
--------------------------------------------------------------------------------
- Fixed reader behavior for `#+/-` inside lists and for line/block comments inside lists. Added list-depth tracking and a skip flag so `;` comments and `#+/-` false branches no longer force an immediate `read()` that trips over list-closing `)`.
- Added a guard for conditional-read skips to tolerate unknown packages (e.g., `sb-ext:` inside `#+sbcl` blocks) by temporarily allowing unknown packages while skipping the form.
- Updated `readtable` comment macro to use a list-aware comment handler.
- `LOAD` now reports byte offsets on read errors to help pinpoint reader issues.
- After these fixes, `rt-package.lsp` and the `#+sbcl` block in `rt.lsp` read successfully. The next blocker when running the package/symbol harness is evaluation of `(declaim ...)` in `rt.lsp` (currently undefined), which raises “Variable 'GET-ENTRY' is not bound”.

Progress update (Feb 5 2026, RT harness blockers)
--------------------------------------------------------------------------------
- Added a stub `declaim` macro and ported the simple `defstruct` macro into `src/init_new.lisp` (plus helpers). `char-code-limit` is now a `defparameter` to avoid macro ordering issues during bootstrap.
- Running the package/symbol harness now progresses past `declaim` and `defstruct` but fails in `rt.lsp` at `(make-hash-table ...)` because TreeCL currently lacks hash table primitives. This is the current hard blocker for executing the ANSI package/symbol tests end-to-end.

Progress update (Feb 5 2026, hash table stubs)
--------------------------------------------------------------------------------
- Added minimal hash table primitives: `make-hash-table`, `gethash` (multiple values), `set-gethash` (for `(setf (gethash ...))`), `remhash`, `clrhash`, and `maphash`. Hash tables use a linear-scan store backed by `HashTableStore`.
- Added `(defsetf gethash set-gethash)` to `src/init_new.lisp`.
- `defstruct` now accepts `(name (:conc-name ...))` forms and honors `:conc-name nil` so accessors match RT expectations.
- RT harness now fails later at missing `assoc` (not implemented), which is the next blocker after hash tables.

Progress update (Feb 5 2026, assoc/rassoc)
--------------------------------------------------------------------------------
- Added minimal `assoc` and `rassoc` primitives (EQL-based, no keyword args). RT harness now progresses further but fails with `TCO Apply not fully implemented for NodeId(...)`, indicating a non-hash/reader issue in the evaluator’s TCO apply path.

Progress update (Feb 5 2026, ANSI package/symbol triage)
--------------------------------------------------------------------------------
- Bootstrap now reads `init_new.lisp` with the current package forced to `COMMON-LISP`, then resets the reader package back to `COMMON-LISP-USER` after bootstrap. This makes init macros/functions land in CL (so exported symbols resolve correctly in CL-USER/tests).
- `init_new.lisp` now exports the core macro/function surface and adds stubs: `eval-when`, `declare`, `handler-case`, plus test helpers (`notnot`, `notnot-mv`, `not-mv`, `eqt`/`eqlt`/`equalt`/`equalpt`, `safely-delete-package`, `+fail-count-limit+`).
- Added `TREECL_DEBUG_DEFPACKAGE` env hook in `prim_sys_defpackage` to trace progress.
- Updated ANSI package/symbol harness to skip `ansi-aux.lsp` (too heavy without full LOOP/conditions) and set `*package*` to `REGRESSION-TEST`/`CL-TEST` before load.
- Current blocker: loading `packages00-aux.lsp` hangs on the first `(report-and-ignore-errors (defpackage "A" ...))`. `TREECL_DEBUG_LOAD=1` shows evaluation stops at that form; likely a `defpackage`/package-system hang that needs further investigation.
