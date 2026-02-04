# TreeCL ANSI Common Lisp Compliance Tasks

Status key: (TODO) or (DONE)

These tasks are ordered with ASDF bootstrap requirements first. When a task is completed, add a short report immediately after it describing status, validity, and implementation quality, and mark the task as (DONE).

## Task 1 - Reader and Readtable Compliance (TODO)
- Goal: Full ANSI reader and readtable behavior so ASDF and the ANSI reader tests load correctly.
- Missing features: `read`, `read-preserving-whitespace`, `read-from-string`, dispatch macros `#.` `#| |#` `#n=` `#n#` `#S` `#A` `#*` `#R` `#C`, numeric token grammar, readtable-case, `*readtable*` and read variables (`*read-base*`, `*read-suppress*`, `*read-eval*`, `*read-default-float-format*`, `*features*`), proper `#+/-` evaluation, proper character literal handling.
- Files: `src/reader.rs`, `src/readtable.rs`, `src/primitives.rs` (reader macros and setters).
- Tests: `tests/ansi-test/reader`.

## Task 2 - Package and Symbol System Compliance (TODO)
- Goal: Full package system and symbol operations required by ASDF and ANSI package/symbol tests.
- Missing features: `defpackage`, `find-symbol` status return values, `export`, `import`, `shadow`, `shadowing-import`, `unintern`, `use-package`, `unuse-package`, `find-all-symbols`, `with-package-iterator`, package accessors (use-list, used-by-list, shadowing-symbols), package nicknames, `rename-package`, correct `*package*` behavior, `gentemp`/`gensym` semantics.
- Files: `src/symbol.rs`, `src/primitives.rs`, `src/eval.rs` (special forms/macros), `src/init.lisp`.
- Tests: `tests/ansi-test/packages`, `tests/ansi-test/symbols`.

## Task 3 - Pathnames and Filesystem API (TODO)
- Goal: ANSI pathname objects and file operations for ASDF and file/pathname tests.
- Missing features: real pathname objects, `pathname`/`namestring`/`parse-namestring`, `make-pathname`, `merge-pathnames`, accessors (`pathname-host/device/directory/name/type/version`), `truename`, `probe-file`, `directory`, `delete-file`, `rename-file`, `ensure-directories-exist`, `file-namestring`, `directory-namestring`, logical pathnames.
- Files: `src/primitives.rs`, `src/streams.rs` (file handles), new pathname module.
- Tests: `tests/ansi-test/pathnames`, `tests/ansi-test/files`.

## Task 4 - Streams and I/O (TODO)
- Goal: ANSI stream API for reading/writing and stream types beyond the current minimal implementation.
- Missing features: `open`, `close` semantics, `with-open-file`, `with-open-stream`, `read-char`, `peek-char`, `unread-char`, `read-line`, `read-byte`, `write-byte`, `finish-output`, `force-output`, `clear-output`, `file-position`, `file-length`, stream predicates, synonym/broadcast/two-way/echo stream behavior, stream element type support.
- Files: `src/streams.rs`, `src/primitives.rs`, `src/eval.rs`.
- Tests: `tests/ansi-test/streams`, `tests/ansi-test/files`.

## Task 5 - Compiler, Load, and Eval Semantics (TODO)
- Goal: ANSI `compile`, `compile-file`, `load`, `eval-when`, and correct macroexpansion semantics needed for ASDF.
- Missing features: `eval-when` phase handling, `compile-file` pipeline (fasl or equivalent), `compile`, `load-time-value`, proper multiple-value returns for `macroexpand` and `macroexpand-1`, `*compile-file-pathname*`, `*compile-file-truename*`, and related dynamic variables.
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
- Missing features: `cond`, `case`, `ecase`, `ccase`, `typecase`, `etypecase`, `progn` variants, `prog`/`prog*`, `do`/`do*`, full `loop` macro, `return`, `return-from` edge cases, `multiple-value-prog1`, `prog1`/`prog2` correctness.
- Files: `src/eval.rs`, `src/init.lisp`.
- Tests: `tests/ansi-test/data-and-control-flow`, `tests/ansi-test/iteration`.

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
