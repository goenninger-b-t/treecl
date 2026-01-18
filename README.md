# TreeCL - Tree Calculus Lisp

TreeCL is a **Lisp implementation** built on top of the **Tree Calculus** (a minimal combinatory logic) in Rust. It compiles Lisp constructs into binary tree structures (`Stem`, `Fork`, `Leaf`) and reduces them using canonical Tree Calculus reduction rules.

## 🌟 Features

### 1. Tree Calculus Core
The foundation is **canonical Tree Calculus** with a single operator `△` and three reduction rules:

| Pattern | Result | Description |
|---------|--------|-------------|
| `△ △ y` | `y` | Identity projection |
| `△ (△ x) y` | `x` | K combinator (constant) |
| `△ (△ x z) y` | `((x y) (z y))` | S combinator |

**Pre-defined Combinators:**
- `K = △ △` — Identity (returns its argument)
- `I = K K` — Also identity (reduces to K)
- `TRIAGE = △` — The primitive operator (NIL)

**Symbolic Printing:** Combinators print as `K`, `I` instead of raw tree structure.

### 2. Language & Evaluator
- **S-Expression Syntax**: Homoiconic code/data representation.
- **Lexical Scoping**: Full support via `let`, `let*`, and closures.
- **Special Forms:**
    - `if`: Conditional branching
    - `quote` (`'x`): Literal data
    - `setq`: Assignment to symbol values
    - `defun`: Global function definition
    - `defvar`, `defparameter`: Variable definition
    - `lambda`: Anonymous functions
    - `progn`: Sequential evaluation
    - `function` (`#'x`): Function namespace capture
    - `macrolet`: Local macro definitions
    - `unwind-protect`, `block`, `return-from`, `tagbody`: Control flow

### 3. Data Types
- **Symbols**: Interned, package-aware (`foo`, `:keyword`, `pkg:sym`)
- **Numbers**: Integers (`i64`), Floats (`f64`), BigInt
- **Strings**: Mutable string buffers
- **Lists**: Cons-cell lists as `Fork(Head, Tail)`
- **Arrays (Vectors)**: O(1) access, syntax `#(1 2 3)` or `[1 2 3]`
- **Closures**: Functions with captured environments
- **Streams**: I/O abstractions (see Streams section)
- **CLOS Instances**: Objects with class and slots

### 4. Standard Library (Primitives)

#### Arithmetic
`+`, `-`, `*`, `/`, `1+`, `1-`, `mod`, `=`, `/=`, `<`, `>`, `<=`, `>=`

#### List Manipulation
`cons`, `car`, `cdr`, `list`, `append`, `reverse`, `nth`, `length`

#### Predicates
`null`, `atom`, `consp`, `listp`, `numberp`, `symbolp`, `eq`, `eql`, `equal`

#### I/O
`print`, `princ`, `terpri`, `format`, `write-string`, `write-char`, `fresh-line`

#### System
- `(gc)` — Force garbage collection, returns freed nodes count
- `(room)` — Display memory statistics

### 5. Streams

TreeCL implements ANSI CL-style streams for I/O operations.

#### Stream Types
- **Standard Streams**: `*standard-input*`, `*standard-output*`, `*error-output*`
- **String Streams**: In-memory I/O to/from strings
- **File Streams**: (Basic support)
- **Broadcast Streams**: Write to multiple destinations

#### Stream Variables
```lisp
*standard-input*   ; #<stream:0> - stdin
*standard-output*  ; #<stream:1> - stdout
*error-output*     ; #<stream:2> - stderr
*trace-output*     ; Same as stdout
*query-io*         ; Same as stdout
*debug-io*         ; Same as stdout
*terminal-io*      ; Same as stdout
```

#### Stream Functions
| Function | Description |
|----------|-------------|
| `(make-string-output-stream)` | Create stream that writes to string |
| `(get-output-stream-string stream)` | Get accumulated string |
| `(make-string-input-stream string)` | Create stream that reads from string |
| `(close stream)` | Close a stream |
| `(write-string string [stream])` | Write string to stream |
| `(write-char char [stream])` | Write character to stream |
| `(fresh-line [stream])` | Newline only if not at column 0 |

#### Format Function
```lisp
(format destination control-string &rest args)
```

**Destinations:**
- `nil` — Return formatted string
- `t` — Write to `*standard-output*`
- `stream` — Write to specified stream

**Format Directives:**
| Directive | Description |
|-----------|-------------|
| `~A` | Aesthetic (human-readable) |
| `~S` | Standard (readable with escapes) |
| `~D` | Decimal integer |
| `~B` | Binary integer |
| `~O` | Octal integer |
| `~X` | Hexadecimal integer |
| `~F` | Floating point |
| `~C` | Character |
| `~%` | Newline |
| `~&` | Fresh line |
| `~~` | Literal tilde |

**Examples:**
```lisp
(format nil "Hello, ~A!" "World")  ; => "Hello, World!"
(format nil "Hex: ~X" 255)          ; => "Hex: ff"
(format t "Count: ~D~%" 42)         ; prints "Count: 42\n"

;; Capture output to string
(let ((s (make-string-output-stream)))
  (format s "Value: ~D" 42)
  (get-output-stream-string s))     ; => "Value: 42"
```

### 6. Memory Management
- **Arena-based Allocation**: All nodes in central `Arena`
- **Automatic GC**: Triggered after 10,000 allocations (configurable)
- **Mark-and-Sweep**: Traces roots (symbols, closures, conditions, arrays)
- **`(room)` Introspection:**
```
=== ROOM ===
Arena:
  Total slots:     42
  Free slots:      10
  Live nodes:      32
Vectors:           2 (15 elements)
Closures:          3
Symbols:           74
GC:
  Threshold:       10000
  Allocs since GC: 156
```

### 7. Object System (CLOS)
Subset of Common Lisp Object System:
- `(defclass name (supers) (slots))`
- `(defgeneric name (args))`
- `(defmethod name ((arg type) ...) body)`
- `(make-instance 'class-name)`
- `(slot-value instance 'slot-name)`
- `(find-class 'name)`, `(class-of instance)`

### 8. Error Handling (Conditions)
- `(error "message")` — Signal errors
- `(handler-bind ...)` — Intercept conditions
- `(restart-bind ...)` — Recovery infrastructure

### 9. Programmable Reader
- **Readtable**: Controls parsing per-character
- **Standard Macros**: `( )`, `'`, `;`, `"`, `` ` ``, `,`, `,@`
- **Dispatch `#`**: `#'`, `#\`, `#(`, `#:`
- **Programmable**: `(set-macro-character char fn)`

### 10. Compiler
Compile Lisp functions to Tree Calculus combinators:
```lisp
(defun square (x) (* x x))
(compile 'square)           ; Returns combinator
(tree-string (compile 'square))  ; "(n ((n sym:*) (n n)))"
(funcall (compile 'square) 5)    ; => 25
```

## 🚀 Usage

### Build & Run
```bash
cargo run
```

### REPL Examples
```lisp
CL-USER> (+ 1 2 3)
6
CL-USER> K
K
CL-USER> I
I
CL-USER> (I I)
K
CL-USER> (gc)
24
CL-USER> (room)
=== ROOM ===
...
CL-USER> (defun fact (n) (if (< n 2) 1 (* n (fact (1- n)))))
FACT
CL-USER> (fact 10)
3628800
CL-USER> *standard-output*
#<stream:1>
CL-USER> (format nil "Hello, ~A!" "Lisp")
"Hello, Lisp!"
```

## 🏗 Architecture

| File | Purpose |
|------|---------|
| `src/arena.rs` | Node storage with allocation counter |
| `src/search.rs` | Tree Calculus reduction engine |
| `src/eval.rs` | Lisp interpreter, environment, GC |
| `src/primitives.rs` | Native function registry |
| `src/printer.rs` | S-expression output with combinator detection |
| `src/reader.rs` | Parser & readtable logic |
| `src/streams.rs` | Stream abstraction layer |
| `src/compiler.rs` | Lisp-to-combinator compiler |
| `src/clos.rs` | Object system (MOP) |
| `src/conditions.rs` | Condition signaling |
| `src/arrays.rs` | Dynamic array storage |
| `src/symbol.rs` | Symbol table & packages |

## Status
- **Core Engine**: Canonical Tree Calculus reduction ✓
- **Lisp Evaluator**: Full evaluation with closures ✓
- **Streams**: ANSI CL stream abstraction ✓
- **Format**: Common format directives ✓
- **Compiler**: Bracket abstraction to combinators ✓
- **CLOS**: Basic object system ✓
- **Conditions**: Error handling ✓
- **Automatic GC**: Threshold-based collection ✓
- **Memory Introspection**: `(room)` primitive ✓
- **Programmable Reader**: Readtables ✓
