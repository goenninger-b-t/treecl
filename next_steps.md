1. Profile `REGRESSION-TEST:DEFTEST` eval-side time in the pathnames harness now that `DEFMETHOD` macro-expansion cost is largely removed.
2. Re-check remaining macro aggregates (`SETF`, `WHEN`, `DEFSTRUCT`, `DEFGENERIC`) and decide whether further fast paths are worth the complexity.
3. Continue using `TREECL_DEBUG_RT_MACRO_TIMING=1` and `TREECL_DEBUG_LOAD_FILE_TIMING=1` after each change; current control runtime baseline is ~1.39s.
