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
  - triage_comb = lambda*f0. lambda* f1. lambda*f2. lambda* z.
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
Progress update (Feb 5 2026, RT harness + package/symbol triage)
--------------------------------------------------------------------------------

- `LOAD` now reads/evals forms sequentially (instead of reading an entire file before eval), so `in-package` and `*package*` changes affect subsequent reads during a load. This was required for the RT harness files (`rt.lsp`, `ansi-aux-macros.lsp`) to intern symbols in the correct package.
- TCO `step_let` now detects special variables and falls back to the full `eval_let` path to preserve dynamic bindings (fixes `*package*` and other `*...*` specials in `let` forms). Without this, `cl-test-package.lsp` shadowed symbols were being added to `REGRESSION-TEST` instead of `CL-TEST`, which made `handler-case` macroexpansion recursive and caused stack overflows.
- `defpackage` now applies `shadow`/`shadowing-import-from` before `:use` so name conflicts (e.g., `DS3` in `packages00-aux.lsp`) no longer abort with “Name conflict on A”.
- `*LOAD-PATHNAME*`, `*LOAD-TRUENAME*`, and `*DEFAULT-PATHNAME-DEFAULTS*` are now exported from `COMMON-LISP` to ensure packages that use `CL` see the same special variables during load.
- New regression tests:
  - `test_let_special_binding_updates_dynamic_value` in `src/eval.rs` (verifies special bindings in `let` update dynamic values).
  - `test_defpackage_shadowing_import_before_use` in `src/primitives.rs` (verifies `defpackage` ordering prevents name conflicts).
- `cargo test -q` passes.
- ANSI package/symbol harness now gets past earlier stack overflow and defpackage conflicts, but stops with an unhandled error `Variable 'WHILE' is not bound` due to the minimal `loop` macro lacking ANSI clauses (`while`, `for`, `in`, etc.). Implementing a proper `loop` macro (Task 11) is the next blocker to run the suite end-to-end.

- Added minimal hash table primitives: `make-hash-table`, `gethash` (multiple values), `set-gethash` (for `(setf (gethash ...))`), `remhash`, `clrhash`, and `maphash`. Hash tables use a linear-scan store backed by `HashTableStore`.
- Added `(defsetf gethash set-gethash)` to `src/init_new.lisp`.
- `defstruct` now accepts `(name (:conc-name ...))` forms and honors `:conc-name nil` so accessors match RT expectations.
- RT harness now fails later at missing `assoc` (not implemented), which is the next blocker after hash tables.

Progress update (Feb 5 2026, assoc/rassoc)
--------------------------------------------------------------------------------

- `assoc` and `rassoc` now parse `:test`, `:test-not`, `:key`, and `:allow-other-keys` keyword arguments, with leftmost keyword wins and unknown keywords rejected unless `:allow-other-keys` is true.
- `:key` of NIL is treated as identity (per ANSI tests). Default test remains `eql`.
- Improper lists or non-cons elements (other than NIL) now signal errors; results still use the generic error path (no dedicated type-error signaling yet).
- Fixed TCO apply path to fall back to tree-calculus reduction when the function object is not a lambda/closure (matching the non-TCO apply fallback). Added a regression test covering tree-calculus fallback in `step_apply`.

Progress update (Feb 5 2026, RT harness run)
--------------------------------------------------------------------------------
- Re-ran `/tmp/ansi_packages_symbols.lsp`; it now loads through `packages/load.lsp` but crashes with a stack overflow (`thread 'worker-0' has overflowed its stack`) before completing the package tests. No additional form context yet.

Progress update (Feb 5 2026, RT harness stack overflow triage)
--------------------------------------------------------------------------------
- Root cause: `cl-test-package.lsp` binds `*package*` using a non-CL `*PACKAGE*` symbol (created via read-before-eval). `maybe_update_current_package` only updated the global current package when the CL `*PACKAGE*` symbol was set, so the binding did not affect the current package and `shadow` ran in REGRESSION-TEST instead of CL-TEST. That left CL-TEST without shadowing symbols, so `handler-case` macro definitions collided with CL and recursed.
- Fix: `maybe_update_current_package` now updates the global current package when *any* symbol named `*PACKAGE*` is set, and mirrors the value into CL:*PACKAGE*. Added a regression test to ensure non-CL `*PACKAGE*` bindings still update current package.

--------------------------------------------------------------------------------

Testing policy (Feb 5 2026)
--------------------------------------------------------------------------------

- Tests have to be created for every new feature being implemented. A task is only completed if such tests and all regression tests have passed. The respective feature tests and all regression tests MUST be run and passed when reporting results.

Progress update (Feb 5 2026, ANSI package/symbol triage)
--------------------------------------------------------------------------------

- Bootstrap now reads `init_new.lisp` with the current package forced to `COMMON-LISP`, then resets the reader package back to `COMMON-LISP-USER` after bootstrap. This makes init macros/functions land in CL (so exported symbols resolve correctly in CL-USER/tests).
- `init_new.lisp` now exports the core macro/function surface and adds stubs: `eval-when`, `declare`, `handler-case`, plus test helpers (`notnot`, `notnot-mv`, `not-mv`, `eqt`/`eqlt`/`equalt`/`equalpt`, `safely-delete-package`, `+fail-count-limit+`).
- Added `TREECL_DEBUG_DEFPACKAGE` env hook in `prim_sys_defpackage` to trace progress.
- Updated ANSI package/symbol harness to skip `ansi-aux.lsp` (too heavy without full LOOP/conditions) and set `*package*` to `REGRESSION-TEST`/`CL-TEST` before load.
- Current blocker: loading `packages00-aux.lsp` hangs on the first `(report-and-ignore-errors (defpackage "A" ...))`. `TREECL_DEBUG_LOAD=1` shows evaluation stops at that form; likely a `defpackage`/package-system hang that needs further investigation.

Progress update (Feb 6 2026, LOOP + defstruct copier)
--------------------------------------------------------------------------------

- Rewrote the minimal `loop` macro in `src/init_new.lisp` to avoid `labels` (not implemented in the evaluator). The new expansion parses clauses and emits a `let` + `tagbody` loop; it supports `for/in/on/from/to/below/=/repeat`, `while`/`until`, `when`/`unless`, `do`, `collect`/`append`/`count`/`sum`/`always`/`thereis`/`return`, and keyword clause variants.
- `defstruct` now emits a `copy-<name>` copier using `sys-struct-ref` + `sys-make-struct` (helper `%defstruct-copier-args`), fixing the missing `copy-entry` in the RT harness.
- Added `test_defstruct_copier` in `src/eval.rs` to verify copier behavior; existing loop subset tests remain in place.
- Tests: `cargo test -q` passes (still emits warnings about unused `ctx` parameters, `unused_mut`, and `ReaderInput::unread`).
- ANSI package/symbol harness (`timeout 120s target/debug/treecl /tmp/ansi_packages_symbols.lsp`) now loads through `packages/load.lsp` but still times out after 120s (exit 124) with no further output, indicating a remaining hang during package tests that needs further triage.

Progress update (Feb 6 2026, hash table hashing + read-eval test)
--------------------------------------------------------------------------------

- Fixed hash table `eql` hashing to be value-based (numeric/char/symbol/string) so equal keys hash to the same bucket; added regression tests `hash_eql_matches_numeric_value` and `hash_equal_matches_cons_structure` in `src/hashtables.rs`.
- Added `test_read_eval_resolves_nested_forms` in `src/primitives.rs` to cover nested `#.` read-time eval resolution via `read_one_from_str`.
- `SYS-STRUCT-REF` now compares type symbols by id first (falling back to case-insensitive name comparison) to reduce symbol-name lookup overhead.
- Tests: `cargo test -q` passes (warnings unchanged).
- ANSI package/symbol harness: `timeout 120s target/debug/treecl /tmp/ansi_packages_symbols.lsp` still exits 124. A 10s debug run (`TREECL_DEBUG_LOAD=1`) processes ~90 forms and is still in early package tests (find-symbol), so overall load performance remains the blocker.

Progress update (Feb 6 2026, perf profile of ANSI package/symbol load)
--------------------------------------------------------------------------------

- Ran `perf record` for 30s on `/tmp/ansi_packages_symbols.lsp` and captured a report. The hottest samples are in SipHash (`core::intrinsics::rotate_left`, `Sip13Rounds::d_rounds`, `RandomState::build_hasher`, `SipHasher13::new_with_keys`) and `hashbrown` lookups, with smaller time in `treecl::arena::Arena::get_unchecked` and a few tree-calculus helpers.
- Interpretation: load-time work is dominated by HashMap hashing/lookup overhead (likely `SymbolTable` and env/package maps) rather than evaluator reduction. This suggests profiling/optimizing symbol and package lookup paths (and possibly switching to a faster hasher) is the next lever for reducing load timeouts.

Progress update (Feb 6 2026, fast hash maps + counters)
--------------------------------------------------------------------------------

- Switched internal `HashMap`/`HashSet` usage to `rustc_hash` `FxHashMap`/`FxHashSet` via a new `src/fastmap.rs` module; updated call sites to use `HashMap::default()`/`HashSet::default()`.
- Added symbol/package lookup counters (find-package/find-symbol/intern) and hash table counters (get/set/rem/clr/maphash) gated by `TREECL_DEBUG_COUNTERS`; `TREECL_DEBUG_COUNTERS_RESET=1` resets counters per load. `prim_load` now prints counter summaries when enabled.
- Added unit tests for the new counters in `src/symbol.rs` and `src/hashtables.rs`.
- Re-profiled with `perf`: SipHash hotspots are gone; the top CPU samples are now in `hashbrown` `RawTable::find/get` and SSE group matching, plus slice precondition checks. Hash lookups remain the dominant cost.
- `cargo test -q` passes; package/symbol harness still times out at 120s.

Progress update (Feb 6 2026, lookup optimization + cumulative counters)
--------------------------------------------------------------------------------

- `find_package` now avoids allocating when the designator is already uppercase by using a `Cow` for lookup; `intern_in_with_status` no longer allocates a `String` unless insertion is needed.
- `LOAD` counters now report per-load deltas without resetting global totals; cumulative counters are printed at process exit when `TREECL_DEBUG_COUNTERS=1`.
- A focused load run (`/tmp/ansi_packages_subset.lsp`) shows the first `gethash`/`sethash` activity during `tests/ansi-test/packages/find-symbol.lsp` (gethash 26, sethash 26). Earlier package aux files show zero hash table ops, so hash usage begins with the test definitions themselves.
- Cumulative load summary (subset run) indicates `find-symbol.lsp` and `find-all-symbols.lsp` dominate elapsed load time (about 21.7s and 9.0s respectively), with other package files under 0.5s. This isolates the main slowdown to those two test files.

Progress update (Feb 6 2026, find-symbol lookup cache)
--------------------------------------------------------------------------------

- Added a per-package `find_symbol_in_package` lookup cache with generation invalidation on package/symbol mutations (intern/export/import/unintern/use/unuse/shadow). Cached hits and misses now avoid repeated use-list scans.
- Added regression test `test_find_symbol_cache_invalidation_after_intern` in `src/symbol.rs`.
- Subset counters run (`TREECL_DEBUG_COUNTERS=1` on `/tmp/ansi_packages_subset.lsp`) shows improved load times: `find-symbol.lsp` ~12.9s, `find-all-symbols.lsp` ~5.6s, total ~18.8s.
- Full package/symbol harness still times out at 120s (`timeout 120s target/debug/treecl /tmp/ansi_packages_symbols.lsp`).

Progress update (Feb 6 2026, minimal pathnames + filesystem primitives)
--------------------------------------------------------------------------------

- Implemented minimal string-backed pathname and filesystem primitives: `pathname`, `namestring`, `make-pathname` (supports :defaults), `merge-pathnames`, `pathname-directory/name/type` (directory returns a keyword list), `pathname-host/device/version` (nil), `probe-file`, `truename`, `directory` (basic glob `*`/`?`), `delete-file`, `rename-file`, `ensure-directories-exist`, `file-namestring`, and `directory-namestring`.
- Added unit tests in `src/primitives.rs` for make-pathname, pathname accessors/namestrings, merge-pathnames defaults, probe-file + directory glob, and ensure-directories-exist.
- Tests: `cargo test -q` passes; regression harness still times out at 120s.

Progress update (Feb 6 2026, pathname objects + parse-namestring)
--------------------------------------------------------------------------------

- Added a lightweight pathname object (`OpaqueValue::Pathname`) backed by `src/pathname.rs` with parsed directory/name/type components; `#P` reader now yields pathname objects.
- Pathname primitives now return pathname objects (`pathname`, `make-pathname`, `merge-pathnames`, `probe-file`, `truename`, `directory`, `rename-file`, `ensure-directories-exist`, `compile-file-pathname`).
- Implemented `parse-namestring` (returns pathname + end index) and added tests for parse-namestring bounds.
- Tests: `cargo test -q` passes; regression harness still times out at 120s.

Progress update (Feb 6 2026, parse-namestring keywords + host/defaults merge)
--------------------------------------------------------------------------------

- `parse-namestring` now parses `:start`, `:end`, and `:junk-allowed` keywords; when junk is allowed, parsing stops at first whitespace and returns the index.
- Added best-effort host/defaults handling: relative namestrings merge against defaults, and host is inherited if provided or in defaults.
- `pathname-host/device/version` now return values from pathname objects (still mostly nil because parsing is minimal).
- Added a `parse-namestring` junk-allowed unit test; `cargo test -q` passes; regression harness still times out at 120s.

Progress update (Feb 6 2026, logical pathname parsing + subset harness)
--------------------------------------------------------------------------------

- `Pathname::from_namestring` now detects logical namestrings (host before `:` with `;` directory separators) and basic Windows drive devices; logical namestrings parse host + directory components + name/type.
- Added a unit test for logical namestring parsing in `parse-namestring`.
- Created a focused pathnames harness (`/tmp/ansi_pathnames_subset.lsp`), but it still times out at 120s (`timeout 120s target/debug/treecl /tmp/ansi_pathnames_subset.lsp`).

Progress update (Feb 6 2026, wild-pathname-p + pathname-match-p + instrumentation)
--------------------------------------------------------------------------------

- Added primitives `pathnamep`, `wild-pathname-p`, and `pathname-match-p` with minimal wildcard matching (name/type globbing and basic directory wild-inferiors handling), plus unit tests.
- Created a step-by-step harness `/tmp/ansi_pathnames_step.lsp` to print before each pathnames file load. The run reaches `wild-pathname-p.lsp` before timing out at 120s, so the stall is within or after that file.

Progress update (Feb 7 2026, filtered LOAD debug for wild-pathname-p)
--------------------------------------------------------------------------------

- Added a `TREECL_DEBUG_LOAD_MATCH` filter to form-level LOAD logging so a single file can be traced without global log spam.
- Ran a focused harness (`/tmp/ansi_pathnames_wild_only.lsp`) with `TREECL_DEBUG_LOAD=1 TREECL_DEBUG_LOAD_MATCH=wild-pathname-p.lsp`; all 36 forms in `wild-pathname-p.lsp` logged and completed, so the stall does not reproduce within that file in isolation.
- The full step harness still times out at 120s before reaching `wild-pathname-p.lsp` (last printed `enough-namestring.lsp`), so the slowdown likely occurs earlier in the pathnames sequence.

Progress update (Feb 7 2026, per-form LOAD timing + pathnames baseline runtime)
--------------------------------------------------------------------------------

- Added `TREECL_DEBUG_LOAD_TIMING=1` support in `prim_load` to emit per-form read/eval durations for files selected by `TREECL_DEBUG_LOAD_MATCH`.
- Re-ran the step harness with `TREECL_DEBUG_LOAD_MATCH=enough-namestring.lsp`; the run still timed out at 120s and only showed file markers through `file-namestring.lsp`.
- Timed `file-namestring.lsp` in the full step harness: all 5 forms completed, with `EVAL` times roughly `0.74s` to `1.07s` and read times below `1ms` per form.
- Timed `wild-pathname-p.lsp` in the full step harness: run reached form `#14` before the 120s timeout; prior forms showed `EVAL` around `0.56s` to `0.92s` each, with negligible read time.
- Control run with larger timeout completed successfully: `timeout 300s target/debug/treecl /tmp/ansi_pathnames_step.lsp` exited 0 and loaded through `parse-namestring.lsp` in `2:39.25`.
- Conclusion: current pathnames timeout behavior is cumulative load/runtime overhead beyond 120s, not a single deterministic hang before `enough-namestring.lsp`.

Progress update (Feb 7 2026, coarse file-level LOAD timing + ranking)
--------------------------------------------------------------------------------

- Added `TREECL_DEBUG_LOAD_FILE_TIMING=1` mode in `prim_load` for coarse per-file elapsed logging (`LOAD FILE TIMING [...]`) and enabled final ranked load summaries in script mode even when symbol/hash counters are disabled.
- Ran the full pathnames step harness with coarse timing: `timeout 240s env TREECL_DEBUG_LOAD_FILE_TIMING=1 target/debug/treecl /tmp/ansi_pathnames_step.lsp` (exit 0).
- Summary output reported `files=28`, `loads=28`, cumulative elapsed `~144.57s`.
- Top elapsed files:
  - `wild-pathname-p.lsp` ~`25.52s`
  - `make-pathname.lsp` ~`15.94s`
  - `pathname-match-p.lsp` ~`9.76s`
  - `pathname.lsp` ~`8.56s`
  - `logical-pathname.lsp` ~`8.36s`
- This confirms a clear optimization priority list for pathnames performance work without requiring noisy per-form logging.
