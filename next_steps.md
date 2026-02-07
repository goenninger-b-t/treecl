1. Re-run the step harness with `TREECL_DEBUG_LOAD_MATCH=enough-namestring.lsp` to pinpoint the last form before the timeout.
2. If it still times out without form logs, add per-form timing to `prim_load` so we can quantify where time is spent.
