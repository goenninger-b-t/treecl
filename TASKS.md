# TreeCL MOP Task List

This file tracks MOP work items across conversations.

## Task 1 — Implement real metaobject classes (DONE)
- Goal: class objects behave as instances of `standard-class` with slot-visible metadata.
- Scope: class metaobjects with slots for name, direct-superclasses/subclasses, direct/effective slots, CPL, finalized-p, instance-size.
- Tests: `tests/mop_metaobject_class_test.lisp`

## Task 2 — Metaobject classes for generic functions, methods, slot definitions (DONE)
- Goal: `standard-generic-function`, `standard-method`, `standard-(direct|effective)-slot-definition` class objects with class-of/slot-value support, plus instance-backed metaobjects.
- Tests: `tests/mop_metaobject_gf_method_slotdef_test.lisp`

## Task 3 — Metaclass & class creation protocol (DONE)
- Goal: `ensure-class-using-class`, `validate-superclass`, `finalize-inheritance` recomputation, `reinitialize-instance`, `change-class`, `update-instance-for-redefined-class`, class default initargs.
- Tests: `tests/mop_class_creation_protocol_test.lisp`

## Task 4 — Slot-definition protocol & slot-missing/unbound (DONE)
- Goal: direct/effective slot-definition classes, make-direct/effective, initfunction env, slot-missing/slot-unbound generics, type enforcement.
- Tests: `tests/mop_slot_definition_protocol_test.lisp`

## Task 5 — Generic function invocation protocol (MOP-level) (DONE)
- Goal: `compute-discriminating-function`, `compute-effective-method`, `compute-effective-method-function`, method caching, `generic-function-argument-precedence-order`, `method-function`, `make-method-lambda`.
- Tests: `tests/mop_generic_invocation_protocol_test.lisp`

## Task 6 — EQL specializers (DONE)
- Goal: `eql` specializers, `intern-eql-specializer`, dispatch support.
- Tests: `tests/mop_eql_specializer_test.lisp`

## Task 7 — Dependents protocol
- Goal: `add-dependent`, `remove-dependent`, `map-dependents`, `update-dependent`.
- Tests: to add when task starts.

## Task 8 — Funcallable instances
- Goal: funcallable standard classes, `set-funcallable-instance-function`, funcallable access.
- Tests: to add when task starts.

## Task 9 — Class/specializer introspection extras
- Goal: `class-direct-methods`, `class-direct-generic-functions`, `specializer-direct-methods`, `specializer-direct-generic-functions`.
- Tests: to add when task starts.

## Task 10 — Accessor/setf completeness
- Goal: proper `(setf <reader>)` generic functions for `:accessor`, full accessor method semantics.
- Tests: to add when task starts.
