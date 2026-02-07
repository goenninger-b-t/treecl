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
  - Log format: `LOAD DEBUG [<filename> #<index>]: <form>`.
  - Timing format:
    - `LOAD DEBUG TIMING [<filename> #<index> READ]: <ms> at-byte=<pos>`
    - `LOAD DEBUG TIMING [<filename> #<index> EVAL]: <ms> total=<ms>`
    - `LOAD FILE TIMING [<filename>]: <ms>`

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

## Outstanding Questions / Next Steps
1. Focus optimization on the top-ranked files first (`wild-pathname-p.lsp`, `make-pathname.lsp`, `pathname-match-p.lsp`), starting with evaluator overhead inside repeated `REGRESSION-TEST:DEFTEST` forms.
2. Add lightweight per-test timing inside `REGRESSION-TEST:DEFTEST` (or equivalent test runner path) to identify whether macroexpansion, assertion helpers, or pathname primitives dominate each file.
3. Keep diagnostic timeout at `>= 180s` for the full pathnames step harness; `120s` remains below baseline.

## Files Modified in Workspace (Uncommitted)
- `src/primitives.rs` (filtered LOAD debug + per-form timing + coarse file timing)
- `src/main.rs` (print ranked load summary when coarse file timing is enabled)
- `references/tasks.md` (triage update)
- `references/knowledge_base.md` (triage update)
- Previously modified in repo (from earlier work): `src/lib.rs`, `src/printer.rs`, `src/reader.rs`, `src/search.rs`, `src/types.rs`, `src/pathname.rs` (pathname feature work)
