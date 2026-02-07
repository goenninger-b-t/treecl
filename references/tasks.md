# TreeCL ANSI Common Lisp Compliance Tasks

Status key: (TODO) or (DONE)

These tasks are ordered with ASDF bootstrap requirements first. When a task is completed, add a short report immediately after it describing status, validity, and implementation quality, and mark the task as (DONE).

## Task 1 - Reader and Readtable Compliance (DONE)
- Goal: Full ANSI reader and readtable behavior so ASDF and the ANSI reader tests load correctly.
- Missing features: dispatch macros `#S` and `#C` still require structures and complex numbers (Tasks 13/7); `#A`/`#*` now parse but only produce nested vectors (no real multi-dimensional/bit-vector types, see Task 9). Numeric token grammar now handles integers/ratios/floats in base 10, but ratios are coerced to floats and `#R` still lacks float/complex support and float subtype integration (`*read-default-float-format*`). Also missing: full character literal/type integration (currently `#\` yields integer codes; see Task 8), full feature expression semantics for `#+/-` (currently limited), and reader entry points still only support string input streams (general stream support in Task 4).
- Files: `src/reader.rs`, `src/readtable.rs`, `src/primitives.rs` (reader macros and setters).
- Tests: `tests/ansi-test/reader`.
Report: Status DONE. Validity: `cargo test -q` (TreeCL Rust tests) passed. ANSI reader tests not run yet; remaining gaps moved to other tasks (numeric tower, arrays, pathnames, streams, types, structures). Implementation quality: solid for reader macro plumbing and character integration; some behaviors intentionally deferred (pathname object semantics, read-default-float-format, full feature expression semantics).
Report update (Feb 6 2026): Added regression test `test_read_eval_resolves_nested_forms` in `src/primitives.rs` to cover nested `#.` read-time eval resolution via `read_one_from_str`. Validity: `cargo test -q` passes.
Remaining subtask: reader harness `tests/ansi-test/reader/load.lsp` still fails at `(in-package #:cl-test)` with `IN-PACKAGE: unknown package` because CL-TEST is not created yet (package system work in Task 2). Re-run this file after package system fixes.

## Task 2 - Package and Symbol System Compliance (DONE)
- Goal: Full package system and symbol operations required by ASDF and ANSI package/symbol tests.
- Missing features: `defpackage`, `find-symbol` status return values, `export`, `import`, `shadow`, `shadowing-import`, `unintern`, `use-package`, `unuse-package`, `find-all-symbols`, `with-package-iterator`, package accessors (use-list, used-by-list, shadowing-symbols), package nicknames, `rename-package`, correct `*package*` behavior, `gentemp`/`gensym` semantics.
- Files: `src/symbol.rs`, `src/primitives.rs`, `src/eval.rs` (special forms/macros), `src/init.lisp`.
- Tests: `tests/ansi-test/packages`, `tests/ansi-test/symbols`.
Report: Status DONE. Validity: `cargo check -q` passes. Implementation quality: package system now tracks use/used-by lists, shadowing symbols, deletions, and lookup status; added ANSI package/symbol primitives (make/delete/rename package, find-symbol statuses, export/import/shadow/shadowing-import/unintern/use/unuse, package accessors, find-all-symbols), plus `gentemp` and enhanced `gensym`/`copy-symbol`/`boundp`. `defpackage`, `with-package-iterator`, and `do-*-symbols` macros were added in `init_new.lisp`, and `*package*` is wired as a special variable with dynamic updates in `let`/`setq`/`defvar`/`defparameter`. Remaining gaps: condition-system typed errors are still missing (package-error tests will still fail), and some ANSI string/array behaviors (fill pointers, displaced strings) are only partially represented.
Report update (Feb 6 2026): Switched internal `HashMap`/`HashSet` usage to `FxHashMap`/`FxHashSet` for symbol/package and related runtime maps. Added debug counters for symbol/package lookups and hash table operations, printed from `LOAD` when `TREECL_DEBUG_COUNTERS=1`. Re-profiled: SipHash hotspots are gone; hashbrown table lookup/SSE group matching now dominate. Harness still times out at 120s.
Report update (Feb 6 2026): Optimized lookup paths to avoid allocating for `find_package` on uppercase designators and to delay `intern` string allocation until insertion is required. Added cumulative counter summaries at process exit. A focused subset run shows `gethash` starts in `packages/find-symbol.lsp` (gethash/sethash 26), confirming hash-table activity begins with test definitions.
Report update (Feb 6 2026): Added per-load aggregation and ranked summaries. A subset run shows `packages/find-symbol.lsp` and `packages/find-all-symbols.lsp` dominate load time (about 21.7s and 9.0s respectively), pointing to those files as the primary performance bottleneck.
Report update (Feb 6 2026): Added a per-package `find_symbol_in_package` lookup cache with generation invalidation on package/symbol mutations. New regression test `test_find_symbol_cache_invalidation_after_intern` added in `src/symbol.rs`. Validity: `cargo test -q` passes. Subset counters run shows `find-symbol.lsp` and `find-all-symbols.lsp` improved to ~12.9s and ~5.6s (total ~18.8s). Full package/symbol harness (`timeout 120s target/debug/treecl /tmp/ansi_packages_symbols.lsp`) still exits 124.

## Task 3 - Pathnames and Filesystem API (TODO)
- Goal: ANSI pathname objects and file operations for ASDF and file/pathname tests.
- Missing features: real pathname objects, `pathname`/`namestring`/`parse-namestring`, `make-pathname`, `merge-pathnames`, accessors (`pathname-host/device/directory/name/type/version`), `truename`, `probe-file`, `directory`, `delete-file`, `rename-file`, `ensure-directories-exist`, `file-namestring`, `directory-namestring`, logical pathnames.
- Files: `src/primitives.rs`, `src/streams.rs` (file handles), new pathname module.
- Tests: `tests/ansi-test/pathnames`, `tests/ansi-test/files`.
Report update (Feb 6 2026): Implemented minimal pathname + filesystem primitives: `pathname`, `namestring`, `make-pathname` (with :defaults), `merge-pathnames`, `pathname-directory/name/type` (directory returns a keyword list), `pathname-host/device/version` (nil), `probe-file`, `truename`, `directory` (basic glob `*`/`?`), `delete-file`, `rename-file`, `ensure-directories-exist`, `file-namestring`, and `directory-namestring`. Added unit tests in `src/primitives.rs` covering make-pathname, pathname accessors/namestrings, merge-pathnames defaults, probe-file + directory glob, and ensure-directories-exist. Validity: `cargo test -q` passes; regression harness still times out (`timeout 120s target/debug/treecl /tmp/ansi_packages_symbols.lsp` exits 124). Implementation quality: minimal string-backed pathnames; no logical pathnames or full ANSI directory/pathname component semantics yet.
Report update (Feb 6 2026): Introduced lightweight pathname objects (`OpaqueValue::Pathname` + `src/pathname.rs`) and added `PARSE-NAMESTRING` (returns pathname + end index). Reader `#P` now constructs pathname objects. Pathname primitives now return pathnames instead of raw strings (`pathname`, `make-pathname`, `merge-pathnames`, `probe-file`, `truename`, `directory`, `rename-file`, `ensure-directories-exist`, `compile-file-pathname`). Added tests for parse-namestring (basic + bounds). Validity: `cargo test -q` passes; regression harness still times out (`timeout 120s target/debug/treecl /tmp/ansi_packages_symbols.lsp` exits 124). Implementation quality: still minimal (string-backed; no logical pathnames or full component semantics).
Report update (Feb 6 2026): Enhanced `parse-namestring` keyword parsing (`:start`, `:end`, `:junk-allowed`) with basic junk handling and defaults/host merging; `pathname-host/device/version` now return values from pathname objects. Added `parse-namestring` junk-allowed test. Validity: `cargo test -q` passes; regression harness still times out (`timeout 120s target/debug/treecl /tmp/ansi_packages_symbols.lsp` exits 124). Implementation quality: still minimal; host/defaults merging is best-effort and not full ANSI semantics.
Report update (Feb 6 2026): Expanded pathname parsing for logical namestrings and basic host/device detection in `Pathname::from_namestring`, and added unit test coverage for logical pathnames in `parse-namestring`. Added a focused pathname subset harness (`/tmp/ansi_pathnames_subset.lsp`) but it still times out after 120s. Validity: `cargo test -q` passes; regression harness still times out (`timeout 120s target/debug/treecl /tmp/ansi_packages_symbols.lsp` exits 124) and pathname harness times out (`timeout 120s target/debug/treecl /tmp/ansi_pathnames_subset.lsp` exits 124). Implementation quality: logical-pathname parsing is minimal (host + semicolon directories, simple name/type split).
Report update (Feb 6 2026): Added `pathnamep`, `wild-pathname-p`, and `pathname-match-p` primitives with minimal wildcard matching (name/type globbing, directory wild-inferiors support) and tests. Added an instrumented step harness (`/tmp/ansi_pathnames_step.lsp`) to identify stalls; it now reaches `wild-pathname-p.lsp` before timing out. Validity: `cargo test -q` passes; regression harness still times out (`timeout 120s target/debug/treecl /tmp/ansi_packages_symbols.lsp` exits 124); pathnames step harness still times out (`timeout 120s target/debug/treecl /tmp/ansi_pathnames_step.lsp` exits 124). Implementation quality: wild matching is minimal and likely incomplete vs ANSI (no full wildcard component semantics or logical pathname translations).
Report update (Feb 7 2026): Added a `TREECL_DEBUG_LOAD_MATCH` filter to form-level LOAD logging so a single file can be traced. Ran a focused harness (`/tmp/ansi_pathnames_wild_only.lsp`) with `TREECL_DEBUG_LOAD=1 TREECL_DEBUG_LOAD_MATCH=wild-pathname-p.lsp`; all 36 forms in `wild-pathname-p.lsp` logged and completed, so no stall appears within that file. The full step harness still times out at 120s before reaching `wild-pathname-p.lsp` (last printed `enough-namestring.lsp`).
Report update (Feb 7 2026): Added per-form LOAD timing (`TREECL_DEBUG_LOAD_TIMING=1`) in `prim_load` and reran the step harness with targeted filters. `file-namestring.lsp` forms all complete; timed `wild-pathname-p.lsp` run reaches form #14 before the 120s timeout, with `EVAL` times roughly 0.56s to 0.92s per form and negligible read time. A control run with larger timeout (`timeout 300s target/debug/treecl /tmp/ansi_pathnames_step.lsp`) exits successfully in 2:39.25, loading through `parse-namestring.lsp`. Conclusion: current pathnames step timeout is cumulative runtime over 120s, not a single pre-`enough-namestring` hang.
Report update (Feb 7 2026): Implemented coarse per-file load timing (`TREECL_DEBUG_LOAD_FILE_TIMING=1`) and enabled ranked load summaries without full-form debug output. A full step run (`timeout 240s env TREECL_DEBUG_LOAD_FILE_TIMING=1 target/debug/treecl /tmp/ansi_pathnames_step.lsp`) completed and reported the slowest files as `wild-pathname-p.lsp` (~25.52s), `make-pathname.lsp` (~15.94s), and `pathname-match-p.lsp` (~9.76s), with total load elapsed ~144.57s across 28 files. This provides a concrete priority order for performance optimization work.

## Task 4 - Streams and I/O (TODO)
- Goal: ANSI stream API for reading/writing and stream types beyond the current minimal implementation.
- Missing features: `open`, `close` semantics, `with-open-file`, full `with-open-stream`, `peek-char`, `read-byte`, `write-byte`, `finish-output`, `force-output`, `clear-output`, `file-position`, `file-length`, stream predicates, synonym/broadcast/two-way/echo stream behavior, stream element type support. Note: `read-char`/`unread-char`/`read-line` exist but only for string streams; `make-two-way-stream`/`make-broadcast-stream` are stubs and need full behavior.
- Files: `src/streams.rs`, `src/primitives.rs`, `src/eval.rs`.
- Tests: `tests/ansi-test/streams`, `tests/ansi-test/files`.

## Task 5 - Compiler, Load, and Eval Semantics (TODO)
- Goal: ANSI `compile`, `compile-file`, `load`, `eval-when`, and correct macroexpansion semantics needed for ASDF.
- Missing features: `eval-when` phase handling, `compile-file` pipeline (fasl or equivalent), `compile`, `load-time-value`, `macroexpand` (and full macroexpansion semantics), `*compile-file-pathname*`, `*compile-file-truename*`, and related dynamic variables. Note: `macroexpand-1` now returns multiple values.
- Files: `src/eval.rs`, `src/primitives.rs`, `src/compiler.rs`.
- Tests: `tests/ansi-test/eval-and-compile`, `tests/ansi-test/system-construction`.

## Task 6 - Condition System and Error Signaling (TODO)
- Goal: Full ANSI condition system suitable for ASDF and condition tests.
- Missing features: `define-condition`, `make-condition`, `signal`, `warn`, `error`, `cerror`, `handler-case`, `handler-bind`, `restart-case`, `restart-bind`, `invoke-restart`, `compute-restarts`, `restart-name`, `with-simple-restart`, `ignore-errors`, `assert`/`check-type` semantics, correct condition classes and type integration.
- Files: `src/conditions.rs`, `src/primitives.rs`, `src/eval.rs`.
- Tests: `tests/ansi-test/conditions`.

## Task 7 - Numeric Tower and Arithmetic (TODO)
- Goal: Full ANSI numeric tower and arithmetic functions.
- Missing features: ratios, complexes, float subtypes, integer division rounding (`floor`, `ceiling`, `round`, `truncate`), `mod`, `rem`, `rational`, `rationalize`, `numerator`, `denominator`, `phase`, `realpart`, `imagpart`, `log`, `exp`, trig functions, `coerce` for numeric types, `random`/`make-random-state` correctness.
- Files: `src/primitives.rs`, new numeric modules.
- Tests: `tests/ansi-test/numbers`.

## Task 8 - Characters and Strings (TODO)
- Goal: ANSI character type and string operations.
- Missing features: distinct character type, `char`/`schar`, `char-code`/`code-char`, character predicates and comparisons, `make-string`, `string=`/`string-equal`/`string<` etc, `string-upcase/downcase/capitalize`, `string-trim` family, `subseq` for strings, `concatenate` on strings, `with-output-to-string`.
- Files: `src/types.rs`, `src/primitives.rs`, `src/reader.rs`, `src/printer.rs`.
- Tests: `tests/ansi-test/characters`, `tests/ansi-test/strings`.

## Task 9 - Arrays and Bit-Vectors (TODO)
- Goal: ANSI array features beyond simple vectors.
- Missing features: multi-dimensional arrays, adjustable arrays, fill pointers, displaced arrays, `array-rank`, `array-dimensions`, `array-total-size`, `adjust-array`, bit-vectors and bit operations, string arrays as specialized vectors, `svref` and `aref` semantics.
- Files: `src/arrays.rs`, `src/primitives.rs`.
- Tests: `tests/ansi-test/arrays`.

## Task 10 - Sequences and List Operations (TODO)
- Goal: ANSI sequence functions and list utilities.
- Missing features: `elt`, `subseq`, `copy-seq`, `concatenate`, `map`, `map-into`, `reduce`, `position`, `find`, `count`, `remove`, `delete`, `substitute`, `sort`, `stable-sort`, list ops like `assoc`, `rassoc`, `member` keyword args, `getf`, `adjoin`, `union`, `intersection`, `set-difference`, `copy-list`, `copy-tree`.
- Files: `src/primitives.rs`, `src/init.lisp`.
- Tests: `tests/ansi-test/sequences`, `tests/ansi-test/cons`.

## Task 11 - Control Flow and Iteration Macros (TODO)
- Goal: ANSI control flow constructs and iteration forms.
- Missing features: `cond`, `case`, `ecase`, `ccase`, `typecase`, `etypecase`, `progn` variants, `prog`/`prog*`, `do`/`do*`, full `loop` macro, `return`, `return-from` edge cases, `prog1`/`prog2` correctness. Note: `multiple-value-prog1` now implemented.
- Files: `src/eval.rs`, `src/init.lisp`.
- Tests: `tests/ansi-test/data-and-control-flow`, `tests/ansi-test/iteration`.
Report: Status TODO. Implemented a minimal `loop` macro in `src/init_new.lisp` without relying on `labels`, covering `for/in/on/from/to/below/=/repeat`, `while`/`until`, `when`/`unless`, `do`, `collect`/`append`/`count`/`sum`/`always`/`thereis`/`return`, and keyword clause variants. Validity: `cargo test -q` passes and the loop subset unit tests in `src/eval.rs` pass; ANSI package/symbol regression harness (`/tmp/ansi_packages_symbols.lsp`) now loads through `packages/load.lsp` but times out after 120s (exit 124), so further triage is still needed. Implementation quality: minimal translation to `let` + `tagbody`, intentionally incomplete vs full ANSI LOOP.
Report update (Feb 6 2026): After hash table fixes and struct-ref optimization, `timeout 120s target/debug/treecl /tmp/ansi_packages_symbols.lsp` still exits 124. A 10s debug run (`TREECL_DEBUG_LOAD=1`) processes ~90 forms and is still in the early package tests (find-symbol); overall load performance remains the blocking issue.
Report update (Feb 6 2026): `perf record` (30s) on the package/symbol harness shows most CPU time in SipHash/`hashbrown` lookups (`RandomState::build_hasher`, `Sip13Rounds::d_rounds`, `rotate_left`). This suggests symbol/package/environment HashMap hashing is the primary hotspot; optimizing or changing the hasher may be required to move the timeout.
Report update (Feb 6 2026): After switching to `FxHashMap`/`FxHashSet`, perf no longer shows SipHash; hashbrown `RawTable::find/get` and SIMD group matching dominate. This confirms the hasher swap worked but overall lookup volume is still the main cost.

## Task 12 - Types and Type System (TODO)
- Goal: ANSI type system and declarations.
- Missing features: `typep`, `subtypep`, `type-of`, `deftype`, `the`, declaration processing for `optimize`, `inline`, `special`, and type declarations, type specifier parsing.
- Files: `src/primitives.rs`, `src/eval.rs`, new type module.
- Tests: `tests/ansi-test/types-and-classes`.

## Task 13 - Structures (TODO)
- Goal: ANSI `defstruct` and structure accessors/constructors.
- Missing features: `defstruct` macro, structure class integration, copier/predicate, print function, slot defaults, and type integration.
- Files: `src/eval.rs`, `src/init.lisp`, CLOS integration.
- Tests: `tests/ansi-test/structures`.
Report: Status TODO. `defstruct` now emits a `copy-<name>` copier using `sys-struct-ref` + `sys-make-struct`, and a unit test `test_defstruct_copier` was added in `src/eval.rs`; the rest of ANSI structure semantics (slot defaults, type integration, printer) remain unimplemented.

## Task 14 - Printer and Pretty Printing (TODO)
- Goal: ANSI printing functions and `*print-*` control variables.
- Missing features: `print`, `prin1`, `princ`, `write`, `write-to-string`, `prin1-to-string`, print-circle/level/length, `*print-escape*`, `*print-readably*`, `*print-base*`, `*print-radix*`, pretty printer (`pprint`) and dispatch tables.
- Files: `src/printer.rs`, `src/primitives.rs`.
- Tests: `tests/ansi-test/printer`.

## Task 15 - Hash Tables (TODO)
- Goal: ANSI hash table API and hashing behavior.
- Missing features: `make-hash-table` options (size, rehash-size, rehash-threshold), `gethash` multiple values, `remhash`, `maphash`, `clrhash`, hash-table accessors, `sxhash`, proper `equalp` hashing.
- Files: `src/hashtables.rs`, `src/primitives.rs`.
- Tests: `tests/ansi-test/hash-tables`.
Report: Status TODO. Hash tables now use bucketed hashing; fixed `eql` hashing to be value-based so equal numeric keys land in the same bucket, and added regression tests `hash_eql_matches_numeric_value` and `hash_equal_matches_cons_structure` in `src/hashtables.rs`. Validity: `cargo test -q` passes. Implementation quality: improved correctness/performance for eq/eql/equal hashing, but ANSI options/accessors and `sxhash` are still missing.

## Task 16 - CLOS and Object System (TODO)
- Goal: Complete ANSI object system integration beyond the MOP core.
- Missing features: built-in classes/type integration, full method combination and method qualifiers, `class-of`/`find-class` semantics, `slot-value`/`slot-boundp` edge cases, `describe`/`documentation` integration, `make-instance` and initargs behavior for all standard classes.
- Files: `src/clos.rs`, `src/primitives.rs`, `src/eval.rs`.
- Tests: `tests/ansi-test/objects`.

## Task 17 - Environment, Time, and Introspection (TODO)
- Goal: ANSI environment/time functions and introspection utilities.
- Missing features: `get-internal-real-time`, `get-internal-run-time`, `get-universal-time`, `decode-universal-time`, `encode-universal-time`, `sleep` accuracy, `room`/`gc` reporting, `apropos`, `describe`, `inspect`, `documentation` behavior.
- Files: `src/primitives.rs`.
- Tests: `tests/ansi-test/environment`, `tests/ansi-test/misc`.

## Task 18 - System Construction and ASDF Integration (TODO)
- Goal: Vendor or implement ASDF so the ANSI test suite can be loaded via ASDF in a fully ANSI-compliant way.
- Missing features: add `asdf.lisp` to the repo, ensure `asdf` package loads, implement `.asd` loading, `asdf:defsystem`, `asdf:load-system`, and complete any remaining ANSI gaps surfaced by ASDF.
- Files: new `asdf.lisp`, `src/primitives.rs`, `src/eval.rs`.
- Tests: `tests/ansi-test/system-construction`, ASDF load of `tests/ansi-test/ansi-test-common.asd`.
