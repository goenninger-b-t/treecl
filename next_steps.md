1. Add hit/miss counters for the simple `SETF` fast path to quantify complex-place fallback rate in `/tmp/ansi_pathnames_step.lsp`.
2. Extend `SETF` fast handling beyond symbol places (where safe), then re-run `TREECL_DEBUG_RT_MACRO_TIMING=1` to validate aggregate reduction.
3. Re-run `TREECL_DEBUG_LOAD_FILE_TIMING=1` after `SETF` work to check movement in top files (`wild-pathname-p.lsp`, `make-pathname.lsp`, `pathname-match-p.lsp`).
