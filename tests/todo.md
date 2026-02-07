1. Real metaobject classes: standard-class, standard-generic-function, standard-method, slot-definition classes as instances with class-of etc. Right now they’re Rust structs/opaque handles, not first-class metaobjects.

2. Metaclass & class creation protocol: full ensure-class-using-class, validate-superclass, finalize-inheritance (real recomputation), reinitialize-instance, change-class, update-instance-for-redefined-class, class-default-initargs/compute-default-initargs.

3. Slot-definition protocol: direct-slot-definition-class / effective-slot-definition-class, make-direct-slot-definition, make-effective-slot-definition, slot-definition-type enforcement, slot-definition-location semantics, and correct initfunction evaluation in environment. Also missing slot-missing/slot-unbound generic functions (we just error).

4. Generic function invocation protocol (MOP-level): compute-discriminating-function, compute-effective-method, compute-effective-method-function, compute-applicable-methods-using-classes caching, generic-function-argument-precedence-order, generic-function-declarations, method-function, make-method-lambda, and full method combination behavior via MOP generics (we hardcode a subset).

5. EQL specializers: eql-specializer, intern-eql-specializer, and dispatch on (eql ...).

6. Dependent protocol: add-dependent, remove-dependent, map-dependents, update-dependent.

7. Funcallable instances: funcallable-standard-class, set-funcallable-instance-function, funcallable-standard-instance-access.

8. Class & specializer introspection extras: class-direct-methods, class-direct-generic-functions, specializer-direct-methods, specializer-direct-generic-functions.

9. Accessor/setf completeness: we generate accessors, but don’t create the canonical (setf <reader>) generic functions for :accessor in the CL way.
