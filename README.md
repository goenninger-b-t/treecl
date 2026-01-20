# TreeCL - Concurrent Lisp on Tree Calculus

TreeCL is an experimental **Lisp implementation** built on top of the **Tree Calculus** (a minimal combinatory logic). It demonstrates how high-level concurrency and functional programming concepts can be built on an extremely minimal computational core.

> **Architecture:** Lisp Source → Tree Calculus Combinators → Reduction Engine → BeamVM-style Scheduler

## 🌟 Key Features

### 1. Actor-Model Concurrency
TreeCL implements Erlang-style concurrency, where isolated processes communicate via message passing.
- **Lightweight Processes**: Each process has its own isolated Arena (heap).
- **Preemptive Multitasking**: A Scheduler manages execution time slices (reductions).
- **Message Passing**: Zero-shared-memory communication using deep-copied message trees.

**Concurrency Primitives:**
- `(spawn fn)`: Spawns a new process running `fn`. Returns the new PID.
- `(send pid msg)`: Sends `msg` to process `pid`. Returns `msg`.
- `(receive)`: Blocks until a message is available in the mailbox.
- `(sleep ms)`: Suspends execution for `ms` milliseconds.
- `(self)`: Returns the current process PID.

**Example:**
```lisp
;; Spawn a worker that prints messages
(defun worker ()
  (let ((msg (receive)))
    (format t "Worker received: ~A~%" msg)
    (worker)))

;; In main process:
(let ((pid (spawn #'worker)))
  (send pid "Hello from Main")
  (sleep 100))
```

### 2. Tree Calculus Core
The foundation is the canonical **Tree Calculus**, which uses a single operator `△` and three reduction rules to perform all computation.
- **Identity**: `△ △ y → y`
- **Constant (K)**: `△ (△ x) y → x`
- **Substitution (S)**: `△ (△ x z) y → ((x y) (z y))`

TreeCL compiles high-level Lisp code (lambdas, variables, applications) into these binary tree structures.

### 3. Compiler-Driven REPL
Unlike traditional interpreters, the TreeCL REPL compile inputs on the fly:
1.  **Read**: Parse S-expressions.
2.  **Compile**: Convert Lisp to Tree Calculus combinators (using bracket abstraction).
3.  **Execute**: The `Scheduler` executes the compiled graph as a Process.

This approach enables **seamless concurrency** in the REPL. When a primitive like `spawn` or `receive` is encountered, it triggers a `SysCall`, which pauses the reduction engine and yields control to the Scheduler.

### 4. Language Features
- **ANSI Common Lisp Subset**: `let`, `lambda`, `if`, `progn`, `defun`, `defvar`.
- **Lexical Scoping**: Full closure support.
- **CLOS Object System**: `defclass`, `defmethod`, `make-instance`.
- **Streams**: `*standard-output*`, `(format)`, string streams.
- **Macros**: `defmacro`, `macrolet`.

## 🛠 Usage

### Prerequisites
- Rust (latest stable)

### Running the REPL
```bash
cargo run --bin treecl
```

### Running Tests
- **Message Passing Verification**:
  ```bash
  cargo run --bin message_test
  ```
  *Verifies process spawning, message deep-copying, and mailbox delivery.*

## 📚 Examples

### Parallel Fibonacci
Spawn two workers to compute Fibonacci numbers in parallel.

```lisp
(defun fib (n)
  (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))

(defun worker (id n)
  (format t "Worker ~A started.~%" id)
  (let ((res (fib n)))
    (format t "Worker ~A result: ~D~%" id res)))

(let ((pid1 (spawn (lambda () (worker 1 25))))
      (pid2 (spawn (lambda () (worker 2 28)))))
  (format t "Spawned workers ~A and ~A~%" pid1 pid2))
```

### Object-Oriented Programming
```lisp
(defclass person ()
  ((name "Unknown")
   (age 0)))

(defmethod describe ((p person))
  (format t "Name: ~A, Age: ~D~%" 
          (slot-value p 'name) 
          (slot-value p 'age)))

(let ((p (make-instance 'person)))
  (set-slot-value p 'name "Alice")
  (set-slot-value p 'age 30)
  (describe p))
```

## 🏗 Architecture

| Component | Description |
|-----------|-------------|
| `src/scheduler.rs` | **The OS Kernel**. Manages PIDs, run queues, and timeslices. Handles `SysCall`s. |
| `src/process.rs` | **Process Control Block**. Owns the `Arena` (heap) and execution context. |
| `src/compiler.rs` | **Compiler**. Translates Lambda Calculus to Combinators (S/K/I). |
| `src/search.rs` | **CPU**. The reduction engine that applies Tree Calculus rules. |
| `src/syscall.rs` | **Interface**. Defines `SysCall` enum (Spawn, Send, Receive). |
| `src/eval.rs` | **Lisp Runtime**. Primitive bridging, environment management, and special forms. |

## 🤝 Contributing
TreeCL is an educational exploration. Key areas for improvement:
- **Garbage Collection**: Currently a simple mark-and-sweep; could be generation/copying.
- **Pattern Matching**: Implement pattern matching in `(receive)`.
- **Error Handling**: Robust process monitoring (links/monitors).

---
*Built with ❤️ in Rust.*
