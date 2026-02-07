# TreeCL Analysis Findings

## 1. Conformance to Tree Calculus

The codebase exhibits **high conformance** to the Tree Calculus specification.

- **Data Structures**: The `Node` enum in `src/arena.rs` perfectly maps to the pure calculus:
  - `Leaf(Nil)` corresponds to the atom (△).
  - `Stem(inner)` corresponds to the unary operator `△ x`.
  - `Fork(left, right)` corresponds to the binary application `x y`.
- **Reduction Rules**: `src/search.rs` correctly implements the three reduction rules (K, S, F) in `reduce_nf_inner` and `reduce_whnf_inner`. The implementation respects the "purity" constraint where only `Nil` leaves are considered valid for reduction delta operators.

## 2. Performance Optimization Potential

Several areas show potential for significant performance improvements:

- **Garbage Collection Overhead**: The current Mark-and-Sweep implementation in `src/process.rs` uses a `HashSet<u32>` to track marked nodes.
  - **Issue**: Hashing `u32` keys and allocating set nodes is essentially slow and cache-inefficient compared to a bit-vector.
  - **Optimization**: Replace `HashSet<u32>` with a `BitSet` or `BitVec` sized to the arena capacity. This would reduce the "Mark" phase complexity from roughly O(N log N) or O(N) with high constants to a tight inner loop.
- **Recursive Algorithms**:
  - **Deep Copy**: The `deep_copy_recursive` function in `src/arena.rs` is prone to stack overflows on deep structures (messages). It should be refactored to an iterative implementation using an explicit heap-allocated stack.
  - **Reduction**: While `reduce_whnf_inner` uses a loop for the spine, it still performs recursive calls for sub-trees (`reduce_whnf_inner(..., left, ...)`). Full Normal Form reduction (`reduce_nf_inner`) is strictly recursive.
- **Arena Entry**: The `Arena` uses an `Entry` enum. Since `Node` is already an enum, this adds a double-indirection/tag overhead. Flattening the storage could improve cache locality.

## 3. Optimizing Garbage Collection

Beyond the `BitSet` optimization mentioned above, the current GC is a simple "Stop-the-World" collector per process.

- **Generational Hypothesis**: Most Lisp objects (cons cells created during evaluation) die young.
- **Proposal**: Implement a **Generational GC**.
  - Split the Arena into a "Nursery" (new allocations) and "Old Generation".
  - Run frequent, fast collections on the Nursery.
  - Promote survivors to the Old Generation.
  - This requires a Write Barrier to track Old-to-New pointers, which might be expensive in a software reducer, but usually pays off for functional languages.
- **Immediate Win**: The `ProcessArena` wrapper in `src/process.rs` currently delegates strictly to the standard `Arena`. Implementing a "bump pointer" allocator within `ProcessArena` (which resets at the end of a timeslice if no GC happened, or just for the nursery) would drastically speed up the allocation of temporary nodes during reduction.

## 4. Missing Features for Colored Tree Calculus Visualization

The current visualization (`src/printer.rs`) implements a "Rainbow" depth-first coloring scheme but lacks semantic connection to Colored Tree Calculus concepts.

- **DAG Visualization**:
  - **Issue**: The `BookTreeBuilder` linearizes the graph into a tree. If a subgraph is shared (common in functional programming and combinator reductions), it is **duplicated** in the visual output.
  - **Constraint**: True graph visualization is essential for understanding "Sharing" in the calculus. A node referenced twice should appear once with two incoming arrows.
  - **Fix**: The `BookDotRenderer` should use the `visited` map to *link* to existing nodes rather than re-emitting them.
- **Semantic Coloring**:
  - **Issue**: Colors are assigned based on depth/index (`PALETTE[(i + depth) % len]`).
  - **Feature**: "Colored" Tree Calculus often implies coloring based on **function** or **combinator identity**. For example, coloring the "spine" of an application differently from the arguments, or highlighting active redexes (the 3 arguments to a delta).
  - **Proposal**: Introduce "Semantic Highlighting" where safe/pure subtrees are colored green, and active redexes (delta at head) are colored red.

## 5. Implementing an Erlang Monitor for TreeCL

The system implements basic Concurrency (Spawn, Send, Receive) but lacks the robust Fault Tolerance primitives of Erlang.

- **Current State**:
  - `Process` struct has a `monitors: HashMap<u64, Pid>` field, but it is effectively unused.
  - `SysCall` enum lacks `Monitor` and `Demonitor`.
- **Implementation Plan**:
    1. **Syscall Support**: Add `SysCall::Monitor(Pid)` -> `Ref` and `SysCall::Demonitor(Ref)` to `src/syscall.rs`.
    2. **Bidirectional State**:
        - Add `monitored_by: HashMap<Ref, Pid>` to `Process` struct. This allows O(1) lookup of who needs to be notified when a process dies.
    3. **Termination Logic**:
        - In `Scheduler` (or `Process::execute_slice` when Status becomes `Terminated` or `Failed`), iterate through `monitored_by`.
        - Send a standard message format: `('DOWN', Ref, Process, Reason)` to each monitoring PID.
    4. **Links vs Monitors**: Distinguish `links` (bidirectional, kill-signal propagation) from `monitors` (unidirectional, informative message).
