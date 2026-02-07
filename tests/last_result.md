Summary: fixed RT harness stack overflow and package shadowing by making LOAD evaluate forms sequentially, adding special-variable handling in the TCO let path, reordering defpackage option application, and exporting load-path specials. The ANSI package/symbol harness now progresses into load.lsp and fails at loop clauses (WHILE unbound), which is the next blocker.

Changes

Sequential LOAD eval so in-package/*package* affect subsequent reads; added reusable reader input plumbing.
Files: primitives.rs, reader.rs
TCO step_let now falls back to full eval_let when special variables are present to preserve dynamic bindings.
File: eval.rs
defpackage now applies shadow / shadowing-import-from before :use, preventing name-conflict aborts.
File: primitives.rs
Exported *LOAD-PATHNAME*, *LOAD-TRUENAME*, *DEFAULT-PATHNAME-DEFAULTS* from COMMON-LISP so CL-using packages see the same specials.
File: primitives.rs
Added regression tests for special bindings in let and defpackage ordering.
Files: eval.rs, primitives.rs
Tests

cargo test -q

Result: passed (74 tests)
ansi_packages_symbols.lsp
Result: failed with Variable 'WHILE' is not bound
Triage

Failure is caused by the minimal loop macro in init_new.lisp which does not implement ANSI loop clauses (while, for, in, collect, etc.). The harness hits (loop while ...) in rt.lsp and later package/symbol files. This is a known Task 11 gap; until loop supports these clauses, the ANSI package/symbol tests cannot run end-to-end.
Knowledge base

Updated knowledge_base.md with the fixes above, new tests, and the current loop blocker.
If you want me to proceed, the next concrete step is to implement a minimal loop macro that supports the clause subset used by rt.lsp, tests/ansi-test/packages, and tests/ansi-test/symbols.
