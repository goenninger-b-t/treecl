# Current Working Context (TreeCL)

## Project/Workspace
- Root: `/var/data/projects/swdev/treecl`
- Goal: Improve ANSI Common Lisp compliance in TreeCL; follow `references/tasks.md` for TODOs and update `references/knowledge_base.md` with new facts.
- Policy: For every new feature, create tests; a task is complete only after feature tests and all regression tests run and pass.

## Recent Focus
- Pathnames step harness keeps timing out at 120s; investigation shifted from “where is it stuck?” to “is this a true hang or cumulative runtime?”
- Added per-form LOAD timing so we can separate reader cost vs evaluator cost.

## Key Files
- `src/primitives.rs`: LOAD implementation + primitives; recently updated to support filtered LOAD logging.
- `references/tasks.md`: task list; updated with recent triage findings.
- `references/knowledge_base.md`: knowledge base; updated with recent triage findings.

## Latest Implementation Change
- `prim_load` now supports filtered logging and timing:
  - `TREECL_DEBUG_LOAD=1` enables form-level LOAD logging.
  - `TREECL_DEBUG_LOAD_MATCH=<substring>` restricts logging to files whose path contains the substring.
  - `TREECL_DEBUG_LOAD_TIMING=1` enables per-form timing in matching files.
  - `TREECL_DEBUG_LOAD_FILE_TIMING=1` enables coarse per-file elapsed logging plus ranked load summary.
  - `TREECL_DEBUG_DEFTEST_TIMING=1` enables split timing for `REGRESSION-TEST:DEFTEST` (`expand` vs `eval`).
  - `TREECL_DEBUG_DEFTEST_MATCH=<substring>` optionally filters which test names get DEFTEST timing logs.
  - `TREECL_DEBUG_RT_MACRO_TIMING=1` enables split timing for arbitrary macros (`MACRO TIMING [<pkg:name>]`).
  - `TREECL_DEBUG_RT_MACRO_MATCH=<substring>` optionally filters which macro names are logged.
  - Log format: `LOAD DEBUG [<filename> #<index>]: <form>`.
  - Timing format:
    - `LOAD DEBUG TIMING [<filename> #<index> READ]: <ms> at-byte=<pos>`
    - `LOAD DEBUG TIMING [<filename> #<index> EVAL]: <ms> total=<ms>`
    - `LOAD FILE TIMING [<filename>]: <ms>`
    - `DEFTEST TIMING [<test-name>]: expand=<ms> eval=<ms> total=<ms>`
    - `MACRO TIMING [<pkg:name>]: expand=<ms> eval=<ms> total=<ms>`
- Evaluator now has a fast expansion path for `REGRESSION-TEST:DEFTEST` that builds the expansion directly in Rust (bypassing expensive macro-body evaluation).
- Evaluator now also includes:
  - fast expansion for `CL-TEST:SIGNALS-ERROR`;
  - fast expansion for `COMMON-LISP:DEFMETHOD` (semantics-preserving macro-shape expansion with fallback);
  - fast-path expansion for common `COMMON-LISP:SETF` places (`symbol`, `car`, `cdr`, `gethash`, `get`, `symbol-value`, `slot-value`, `funcallable-standard-instance-access`, `readtable-case`);
  - direct evaluator handling for `COMMON-LISP:LET*` and `COMMON-LISP:COND` (in both step and non-step application paths, before macro expansion);
  - direct evaluator handling for `COMMON-LISP:OR` (in both step and non-step application paths, before macro expansion);
  - cached env-flag lookups (`OnceLock`) for macro timing toggles to avoid repeated hot-path `std::env::var` calls.

## Harnesses/Artifacts
- `/tmp/ansi_pathnames_step.lsp`: step-by-step loader that prints before each pathnames file load.
- `/tmp/ansi_pathnames_wild_only.lsp`: minimal harness to load only wild-pathname tests after RT/bootstrap.
- `/tmp/ansi_pathnames_wild_debug.log`: log from step harness with filtered LOAD debug (timeout).
- `/tmp/ansi_pathnames_wild_only.log`: log from the focused wild-pathname harness (completed).
- `/tmp/ansi_pathnames_enough_debug.log`: step harness with `TREECL_DEBUG_LOAD_MATCH=enough-namestring.lsp` (timeout).
- `/tmp/ansi_pathnames_file_namestring_timing.log`: step harness with timing focused on `file-namestring.lsp`.
- `/tmp/ansi_pathnames_wild_timing.log`: step harness with timing focused on `wild-pathname-p.lsp`.
- `/tmp/ansi_pathnames_step_300.log`: step harness control run with 300s timeout (completed).
- `/tmp/ansi_pathnames_file_timing_summary.log`: step harness run with coarse file timing + ranked summary.
- `/tmp/ansi_pathnames_deftest_split.log`: step harness run with `DEFTEST` split timing focused on `WILD-PATHNAME-P.*`.
- `/tmp/ansi_pathnames_deftest_split_fast.log`: post-optimization `DEFTEST` split timing run.
- `/tmp/ansi_pathnames_file_timing_summary_fast.log`: post-optimization coarse file timing run.
- `/tmp/ansi_pathnames_step_120_after_fast.log`: 120s control run after optimization (completed).
- `/tmp/ansi_pathnames_macro_signals_fast.log`: targeted macro timing run for `CL-TEST:SIGNALS-ERROR`.
- `/tmp/ansi_pathnames_rt_macro_timing.log`: full macro timing run (all macros).
- `/tmp/ansi_pathnames_rt_macro_timing_after_setf_fast.log`: full macro timing run after setf fast path.
- `/tmp/ansi_pathnames_file_timing_after_setf_fast.log`: coarse file timing run after latest macro changes.
- `/tmp/ansi_pathnames_rt_macro_timing_after_letstar_cond_eval.log`: full macro timing run after evaluator-level LET*/COND handling.
- `/tmp/ansi_pathnames_file_timing_after_letstar_cond_eval.log`: coarse file timing run after evaluator-level LET*/COND handling.
- `/tmp/ansi_pathnames_step_after_letstar_cond_eval.log`: 120s control run after evaluator-level LET*/COND handling.
- `/tmp/ansi_pathnames_rt_macro_timing_after_setf_place_fast.log`: full macro timing run after broader SETF place fast path.
- `/tmp/ansi_pathnames_file_timing_after_setf_place_fast.log`: coarse file timing run after broader SETF place fast path.
- `/tmp/ansi_pathnames_step_after_setf_place_fast.log`: 120s control run after broader SETF place fast path.
- `/tmp/ansi_pathnames_rt_macro_timing_after_or_direct_final.log`: full macro timing run after evaluator-level OR handling.
- `/tmp/ansi_pathnames_file_timing_after_or_direct_final.log`: coarse file timing run after evaluator-level OR handling.
- `/tmp/ansi_pathnames_step_after_or_direct_final.log`: 120s control run after evaluator-level OR handling.
- `/tmp/ansi_pathnames_rt_macro_timing_after_defmethod_fast.log`: full macro timing run after safe DEFMETHOD fast expansion.
- `/tmp/ansi_pathnames_file_timing_after_defmethod_fast.log`: coarse file timing run after safe DEFMETHOD fast expansion.
- `/tmp/ansi_pathnames_step_after_defmethod_fast.log`: 120s control run after safe DEFMETHOD fast expansion.

## Latest Findings
- Re-run with `TREECL_DEBUG_LOAD_MATCH=enough-namestring.lsp` still timed out at 120s, but showed only file-level markers up to `file-namestring.lsp`.
- After adding per-form timing, `file-namestring.lsp` completes all 5 forms and the step harness continues through `directory-namestring.lsp`, `host-namestring.lsp`, `enough-namestring.lsp`, and into `wild-pathname-p.lsp`.
- Timed trace of `wild-pathname-p.lsp` in the full step run reached form `#14` before 120s timeout; prior `EVAL` durations were roughly `0.56s` to `0.92s` per form.
- Control run with larger timeout finished successfully:
  - `timeout 300s target/debug/treecl /tmp/ansi_pathnames_step.lsp` exited 0.
  - Measured elapsed wall time: `2:39.25`.
- Coarse file-level timing run completed and produced ranked hot files for the pathnames sequence:
  - `wild-pathname-p.lsp` ~`25.52s`
  - `make-pathname.lsp` ~`15.94s`
  - `pathname-match-p.lsp` ~`9.76s`
  - `pathname.lsp` ~`8.56s`
  - `logical-pathname.lsp` ~`8.36s`
- Full coarse-timed load summary:
  - `files=28`, `loads=28`, cumulative elapsed `~144.57s`.
- `DEFTEST` split timing (focused on `WILD-PATHNAME-P.*`) confirms macro expansion dominates:
  - 36 tests total: expand sum `~16804ms` vs eval sum `~5804ms`.
  - Per-test averages: expand `~466.8ms`, eval `~161.2ms`.
  - Several slowest tests (`WILD-PATHNAME-P.32`, `.ERROR.2`, `.ERROR.4`) still show expansion as the larger share.
- After adding fast `REGRESSION-TEST:DEFTEST` expansion:
  - Same 36 `WILD-PATHNAME-P.*` tests now show expand sum `~1.03ms` vs eval sum `~5822ms`.
  - Expansion average dropped from `~466.8ms` to `~0.03ms` per test.
  - `wild-pathname-p.lsp` file elapsed dropped from `~25.52s` to `~4.48s` (~`82.4%` reduction, ~`5.69x` faster).
  - Full step-harness cumulative elapsed dropped from `~144.57s` to `~26.93s` (~`81.4%` reduction, ~`5.37x` faster).
  - `timeout 120s target/debug/treecl /tmp/ansi_pathnames_step.lsp` now completes successfully (`exit 0`).
- Targeted `CL-TEST:SIGNALS-ERROR` macro timing produced zero hits in the pathnames step load (`TREECL_DEBUG_RT_MACRO_TIMING=1 TREECL_DEBUG_RT_MACRO_MATCH=CL-TEST:SIGNALS-ERROR`), confirming these forms are not macroexpanded during load (they are inside quoted `DEFTEST` bodies).
- Full macro timing (`TREECL_DEBUG_RT_MACRO_TIMING=1`) shows dominant load-time macro costs are currently:
  - `COMMON-LISP:LET*` (largest aggregate total),
  - `COMMON-LISP:COND`,
  - `REGRESSION-TEST:DEFTEST` (mostly eval side after expansion fast path),
  - `COMMON-LISP:SETF` (high aggregate expansion time).
- Adding a simple-symbol `SETF` fast path did not produce a measurable aggregate `SETF` reduction in the full timing run, implying most expensive `SETF` expansions likely use complex places and still fall back to macro-body evaluation.
- After adding evaluator-level `LET*` and `COND` handling:
  - `COMMON-LISP:LET*` and `COMMON-LISP:COND` disappear from macro timing aggregates (they no longer macroexpand on this path).
  - Macro timing top entries become `REGRESSION-TEST:DEFTEST` (mostly eval-side) and `COMMON-LISP:SETF` (expansion-heavy).
  - Coarse file timing improves from ~`34.52s` to ~`28.73s` total (~`16.8%` faster).
  - 120s control run completes in ~`27.67s`.
- After broadening `SETF` fast-path place handling:
  - `COMMON-LISP:SETF` macro aggregate drops from ~`33055ms` total (`expand ~32573ms`) to ~`222ms` total (`expand ~7.4ms`).
  - Coarse file timing improves from ~`28.73s` to ~`1.68s` total (~`94.15%` faster).
  - 120s control run completes in ~`3.90s`.
  - Remaining top macro timing contributors shift to `COMMON-LISP:DEFMETHOD` and `COMMON-LISP:OR`.
- After adding evaluator-level `OR` handling:
  - `COMMON-LISP:OR` disappears from macro timing aggregates (no `OR` hits in aggregate output).
  - Control runtime improves from ~`3.90s` to ~`3.19s`.
- After adding safe `DEFMETHOD` fast expansion:
  - `COMMON-LISP:DEFMETHOD` aggregate drops from ~`1560.3ms` total (`expand ~1500.5ms`) to ~`45.5ms` total (`expand ~2.6ms`).
  - Coarse load summary improves to ~`1044ms`.
  - 120s control runtime improves from ~`3.19s` to ~`1.39s`.
  - Current top macro contributors are now `REGRESSION-TEST:DEFTEST` (mostly eval-side), `SETF`, `WHEN`, and `DEFSTRUCT`.
- Conclusion: current evidence points to cumulative runtime over the 120s timeout window, not a single hard stall before `enough-namestring.lsp`.

## Tests Recently Run
- `cargo test -q` (passes; warnings about unused `mut`/`ctx` and `ReaderInput::unread`).
- `timeout 120s env TREECL_DEBUG_LOAD=1 TREECL_DEBUG_LOAD_MATCH=wild-pathname-p.lsp target/debug/treecl /tmp/ansi_pathnames_step.lsp` (exit 124; timeout before wild-pathname file).
- `timeout 120s env TREECL_DEBUG_LOAD=1 TREECL_DEBUG_LOAD_MATCH=wild-pathname-p.lsp target/debug/treecl /tmp/ansi_pathnames_wild_only.lsp` (completed, log shows all 36 forms).
- `timeout 120s env TREECL_DEBUG_LOAD=1 TREECL_DEBUG_LOAD_MATCH=enough-namestring.lsp target/debug/treecl /tmp/ansi_pathnames_step.lsp` (exit 124; no per-form hits for enough-namestring).
- `timeout 120s env TREECL_DEBUG_LOAD=1 TREECL_DEBUG_LOAD_TIMING=1 TREECL_DEBUG_LOAD_MATCH=file-namestring.lsp target/debug/treecl /tmp/ansi_pathnames_step.lsp` (exit 124; file-namestring forms timed and completed).
- `timeout 120s env TREECL_DEBUG_LOAD=1 TREECL_DEBUG_LOAD_TIMING=1 TREECL_DEBUG_LOAD_MATCH=wild-pathname-p.lsp target/debug/treecl /tmp/ansi_pathnames_step.lsp` (exit 124; reached wild form #14).
- `timeout 300s target/debug/treecl /tmp/ansi_pathnames_step.lsp` (exit 0; elapsed `2:39.25`).
- `timeout 240s env TREECL_DEBUG_LOAD_FILE_TIMING=1 target/debug/treecl /tmp/ansi_pathnames_step.lsp` (exit 0; ranked top files printed).
- `timeout 240s env TREECL_DEBUG_DEFTEST_TIMING=1 TREECL_DEBUG_DEFTEST_MATCH=WILD-PATHNAME-P. target/debug/treecl /tmp/ansi_pathnames_step.lsp` (exit 0; split expand/eval timing for 36 tests).
- `timeout 240s env TREECL_DEBUG_DEFTEST_TIMING=1 TREECL_DEBUG_DEFTEST_MATCH=WILD-PATHNAME-P. target/debug/treecl /tmp/ansi_pathnames_step.lsp` after fast path (exit 0; expansion cost effectively eliminated).
- `timeout 240s env TREECL_DEBUG_LOAD_FILE_TIMING=1 target/debug/treecl /tmp/ansi_pathnames_step.lsp` after fast path (exit 0; total elapsed ~26.93s).
- `timeout 120s target/debug/treecl /tmp/ansi_pathnames_step.lsp` after fast path (exit 0).
- `timeout 240s env TREECL_DEBUG_RT_MACRO_TIMING=1 TREECL_DEBUG_RT_MACRO_MATCH=CL-TEST:SIGNALS-ERROR target/debug/treecl /tmp/ansi_pathnames_step.lsp` (exit 0; no matching macro timing hits).
- `timeout 240s env TREECL_DEBUG_RT_MACRO_TIMING=1 target/debug/treecl /tmp/ansi_pathnames_step.lsp` (exit 0; macro aggregate shows `LET*`/`COND`/`SETF` dominant).
- `timeout 240s env TREECL_DEBUG_RT_MACRO_TIMING=1 target/debug/treecl /tmp/ansi_pathnames_step.lsp` after evaluator-level `LET*`/`COND` (exit 0; `LET*`/`COND` no longer appear in macro aggregates).
- `timeout 240s env TREECL_DEBUG_LOAD_FILE_TIMING=1 target/debug/treecl /tmp/ansi_pathnames_step.lsp` after evaluator-level `LET*`/`COND` (exit 0; total ~28.73s).
- `timeout 120s target/debug/treecl /tmp/ansi_pathnames_step.lsp` after evaluator-level `LET*`/`COND` (exit 0; elapsed ~27.67s).
- `timeout 240s env TREECL_DEBUG_RT_MACRO_TIMING=1 target/debug/treecl /tmp/ansi_pathnames_step.lsp` after broader `SETF` place fast path (exit 0; `SETF` aggregate reduced to ~222ms total).
- `timeout 240s env TREECL_DEBUG_LOAD_FILE_TIMING=1 target/debug/treecl /tmp/ansi_pathnames_step.lsp` after broader `SETF` place fast path (exit 0; total ~1.68s).
- `timeout 120s target/debug/treecl /tmp/ansi_pathnames_step.lsp` after broader `SETF` place fast path (exit 0; elapsed ~3.90s).
- `cargo test -q` after broader `SETF` place fast path + tests (passes; 101 tests in core suite).
- `cargo test -q` after evaluator-level `OR` handling (passes; 102 tests in core suite).
- `timeout 240s env TREECL_DEBUG_RT_MACRO_TIMING=1 target/debug/treecl /tmp/ansi_pathnames_step.lsp` after evaluator-level `OR` handling (exit 0; aggregate no longer includes `COMMON-LISP:OR`).
- `timeout 240s env TREECL_DEBUG_LOAD_FILE_TIMING=1 target/debug/treecl /tmp/ansi_pathnames_step.lsp` after evaluator-level `OR` handling (exit 0; load summary in ~1.3-1.9s across repeated runs).
- `timeout 120s target/debug/treecl /tmp/ansi_pathnames_step.lsp` after evaluator-level `OR` handling (exit 0; elapsed ~3.19s).
- `cargo test -q` after safe `DEFMETHOD` fast expansion + tests (passes; 104 tests in core suite).
- `timeout 240s env TREECL_DEBUG_RT_MACRO_TIMING=1 target/debug/treecl /tmp/ansi_pathnames_step.lsp` after safe `DEFMETHOD` fast expansion (exit 0; `DEFMETHOD` aggregate ~45.5ms total).
- `timeout 240s env TREECL_DEBUG_LOAD_FILE_TIMING=1 target/debug/treecl /tmp/ansi_pathnames_step.lsp` after safe `DEFMETHOD` fast expansion (exit 0; load summary ~1044ms).
- `timeout 120s target/debug/treecl /tmp/ansi_pathnames_step.lsp` after safe `DEFMETHOD` fast expansion (exit 0; elapsed ~1.39s).

## Outstanding Questions / Next Steps
1. Profile `REGRESSION-TEST:DEFTEST` eval-side work (not expansion-side) now that major macro-expansion costs are largely removed.
2. Evaluate whether remaining macro contributors (`SETF`, `WHEN`, `DEFSTRUCT`, `DEFGENERIC`) need additional fast paths or are acceptable at current ~1.4s runtime.
3. Keep re-running `TREECL_DEBUG_RT_MACRO_TIMING=1` and `TREECL_DEBUG_LOAD_FILE_TIMING=1` after each optimization to track regressions/movement.

## Files Modified in Workspace (Uncommitted)
- `src/primitives.rs` (filtered LOAD debug + per-form timing + coarse file timing)
- `src/eval.rs` (`DEFTEST`/macro timing instrumentation + fast macro/evaluator paths including `SETF`, `LET*`, `COND`, and `OR`)
- `src/main.rs` (print ranked load summary when coarse file timing is enabled)
- `references/tasks.md` (triage update)
- `references/knowledge_base.md` (triage update)
- Previously modified in repo (from earlier work): `src/lib.rs`, `src/printer.rs`, `src/reader.rs`, `src/search.rs`, `src/types.rs`, `src/pathname.rs` (pathname feature work)
