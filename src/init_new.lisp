
;;; TreeCL Standard Library (Prelude)

(in-package "COMMON-LISP")

(defmacro when (test &rest body)
  `(if ,test (progn ,@body)))

(defmacro unless (test &rest body)
  `(if ,test nil (progn ,@body)))

(defmacro or (&rest args)
  (if (null args)
      nil
      (if (null (cdr args))
          (car args)
          (let ((gp (gensym)))
            `(let ((,gp ,(car args)))
               (if ,gp ,gp (or ,@(cdr args))))))))

(defmacro and (&rest args)
  (if (null args)
      t
      (if (null (cdr args))
          (car args)
          `(if ,(car args) (and ,@(cdr args)) nil))))

(defmacro cond (&rest clauses)
  (if (null clauses)
      nil
      (let ((clause (car clauses))
            (rest (cdr clauses)))
        (if (null clause)
            `(cond ,@rest)
            (let ((test (car clause))
                  (body (cdr clause)))
              (if (null body)
                  `(let ((temp ,test))
                     (if temp temp (cond ,@rest)))
                  `(if ,test (progn ,@body) (cond ,@rest))))))))

(defmacro eval-when (situations &rest body)
  (declare (ignore situations))
  `(progn ,@body))

(defmacro declaim (&rest decls)
  nil)

(defmacro declare (&rest decls)
  nil)

(defparameter char-code-limit 1114112)

(defun %defstruct-slot-name (spec)
  (if (consp spec) (car spec) spec))

(defun %defstruct-conc-name (name)
  (if (consp name)
      (let* ((opts (cdr name))
             (opt (assoc :conc-name opts)))
        (if opt (cadr opt) (concatenate 'string (symbol-name (car name)) "-")))
      (concatenate 'string (symbol-name name) "-")))

(defun %defstruct-accessor-name (prefix slot)
  (let ((p (cond ((null prefix) "")
                 ((symbolp prefix) (symbol-name prefix))
                 ((stringp prefix) prefix)
                 (t ""))))
    (intern (concatenate 'string p (symbol-name slot)))))

(defun %defstruct-accessors (name prefix slots idx)
  (if (null slots)
      nil
      (let* ((slot (car slots))
             (acc (%defstruct-accessor-name prefix slot)))
        (cons `(defun ,acc (obj) (sys-struct-ref obj ,idx ',name))
              (%defstruct-accessors name prefix (cdr slots) (+ idx 1))))))

(defun %defstruct-copier-args (name slots idx)
  (if (null slots)
      nil
      (let ((slot (car slots)))
        (cons `',slot
              (cons `(sys-struct-ref obj ,idx ',name)
                    (%defstruct-copier-args name (cdr slots) (+ idx 1)))))))

(defmacro defstruct (name &rest slots)
  (let* ((struct-name (if (consp name) (car name) name))
         (slot-names (mapcar #'%defstruct-slot-name slots))
         (conc-name (%defstruct-conc-name name))
         (maker (intern (concatenate 'string "MAKE-" (symbol-name struct-name))))
         (copier (intern (concatenate 'string "COPY-" (symbol-name struct-name))))
         (pred (intern (concatenate 'string (symbol-name struct-name) "-P")))
         (accessors (%defstruct-accessors struct-name conc-name slot-names 0))
         (copy-args (%defstruct-copier-args struct-name slot-names 0)))
    `(progn
       (defun ,maker (&rest args)
         (apply #'sys-make-struct ',struct-name ',slot-names args))
       (defun ,copier (obj)
         (sys-make-struct ',struct-name ',slot-names ,@copy-args))
       (defun ,pred (obj)
         (sys-struct-p obj ',struct-name))
       ,@accessors
       ',struct-name)))

;;; Minimal ANSI test harness helper (keep in CL-USER for tests)
(defun common-lisp-user::compile-and-load (pathspec &rest args)
  (declare (ignore args))
  (load-and-compile-minimal pathspec))

(defmacro in-package (designator)
  ;; Ensure the designator is not evaluated (ANSI behavior).
  (if (and (consp designator) (eq (car designator) 'quote))
      `(funcall 'in-package ,designator)
      `(funcall 'in-package ',designator)))

(defmacro defpackage (name &rest options)
  `(sys-defpackage ',name ',options))

(defmacro with-package-iterator ((name package-list &rest symbol-types) &body body)
  (let ((entries (gensym "ENTRIES"))
        (entry (gensym "ENTRY")))
    `(let ((,entries (sys-package-iterator-entries ,package-list ',symbol-types)))
       (flet ((,name ()
                (if (null ,entries)
                    (values nil nil nil nil)
                    (let ((,entry (car ,entries)))
                      (setq ,entries (cdr ,entries))
                      (values t (car ,entry) (cadr ,entry) (caddr ,entry))))))
         ,@body))))

(defmacro do-symbols ((var &optional (package '*package*) result) &body body)
  (let ((iter (gensym "ITER"))
        (pkg (gensym "PKG"))
        (more (gensym "MORE"))
        (sym (gensym "SYM"))
        (access (gensym "ACCESS"))
        (pp (gensym "PP")))
    `(let ((,pkg ,package))
       (with-package-iterator (,iter (list ,pkg) :internal :external :inherited)
         (block nil
           (tagbody
            start
              (multiple-value-bind (,more ,sym ,access ,pp) (,iter)
                (declare (ignore ,access ,pp))
                (unless ,more (return ,result))
                (let ((,var ,sym))
                  ,@body)
                (go start))))))))

(defmacro do-external-symbols ((var &optional (package '*package*) result) &body body)
  (let ((iter (gensym "ITER"))
        (pkg (gensym "PKG"))
        (more (gensym "MORE"))
        (sym (gensym "SYM"))
        (access (gensym "ACCESS"))
        (pp (gensym "PP")))
    `(let ((,pkg ,package))
       (with-package-iterator (,iter (list ,pkg) :external)
         (block nil
           (tagbody
            start
              (multiple-value-bind (,more ,sym ,access ,pp) (,iter)
                (declare (ignore ,access ,pp))
                (unless ,more (return ,result))
                (let ((,var ,sym))
                  ,@body)
                (go start))))))))

(defmacro do-all-symbols ((var &optional result) &body body)
  (let ((iter (gensym "ITER"))
        (more (gensym "MORE"))
        (sym (gensym "SYM"))
        (access (gensym "ACCESS"))
        (pp (gensym "PP")))
    `(with-package-iterator (,iter (list-all-packages) :internal :external :inherited)
       (block nil
         (tagbody
          start
            (multiple-value-bind (,more ,sym ,access ,pp) (,iter)
              (declare (ignore ,access ,pp))
              (unless ,more (return ,result))
              (let ((,var ,sym))
                ,@body)
              (go start)))))))




(defun not (x) (if x nil t))
(defun null (x) (if x nil t))

(defun notnot (x) (if x t nil))

(defmacro notnot-mv (form)
  `(notnot-mv-fn (multiple-value-list ,form)))

(defun notnot-mv-fn (results)
  (if (null results)
      (values)
      (apply #'values
             (notnot (first results))
             (rest results))))

(defmacro not-mv (form)
  `(not-mv-fn (multiple-value-list ,form)))

(defun not-mv-fn (results)
  (if (null results)
      (values)
      (apply #'values
             (not (first results))
             (rest results))))

(defun eqt (x y)
  (apply #'values (mapcar #'notnot (multiple-value-list (eq x y)))))

(defun eqlt (x y)
  (apply #'values (mapcar #'notnot (multiple-value-list (eql x y)))))

(defun equalt (x y)
  (apply #'values (mapcar #'notnot (multiple-value-list (equal x y)))))

(defun equalpt (x y)
  (apply #'values (mapcar #'notnot (multiple-value-list (equal x y)))))

(defun mapcar (fn list &rest more-lists)
  (if (null more-lists)
      (if (null list)
          nil
          (cons (funcall fn (car list))
                (mapcar fn (cdr list))))
      (let ((lists (cons list more-lists)))
        (if (some #'null lists)
            nil
            (cons (apply fn (mapcar #'car lists))
                  (apply #'mapcar fn (mapcar #'cdr lists)))))))

(defun some (pred list)
  (if (null list)
      nil
      (if (funcall pred (car list))
          t
          (some pred (cdr list)))))

(defun append (l1 l2)
  (if (null l1)
      l2
      (cons (car l1) (append (cdr l1) l2))))

(defun reverse (list)
  (let ((result nil))
    (dolist (x list)
      (setq result (cons x result)))
    result))

(defun nreverse (list)
  (reverse list))

(defun caar (x) (car (car x)))
(defun cadr (x) (car (cdr x)))
(defun cdar (x) (cdr (car x)))
(defun cddr (x) (cdr (cdr x)))
(defun caaar (x) (car (car (car x))))
(defun caadr (x) (car (car (cdr x))))
(defun cadar (x) (car (cdr (car x))))
(defun caddr (x) (car (cdr (cdr x))))
(defun cdaar (x) (cdr (car (car x))))
(defun cdadr (x) (cdr (car (cdr x))))
(defun cddar (x) (cdr (cdr (car x))))
(defun cdddr (x) (cdr (cdr (cdr x))))
(defun caaaar (x) (car (car (car (car x)))))
(defun caaadr (x) (car (car (car (cdr x)))))
(defun caadar (x) (car (car (cdr (car x)))))
(defun caaddr (x) (car (car (cdr (cdr x)))))
(defun cadaar (x) (car (cdr (car (car x)))))
(defun cadadr (x) (car (cdr (car (cdr x)))))
(defun caddar (x) (car (cdr (cdr (car x)))))
(defun cadddr (x) (car (cdr (cdr (cdr x)))))
(defun cdaaar (x) (cdr (car (car (car x)))))
(defun cdaadr (x) (cdr (car (car (cdr x)))))
(defun cdadar (x) (cdr (car (cdr (car x)))))
(defun cdaddr (x) (cdr (car (cdr (cdr x)))))
(defun cddaar (x) (cdr (cdr (car (car x)))))
(defun cddadr (x) (cdr (cdr (car (cdr x)))))
(defun cdddar (x) (cdr (cdr (cdr (car x)))))
(defun cddddr (x) (cdr (cdr (cdr (cdr x)))))

(defun first (x) (car x))
(defun second (x) (cadr x))
(defun third (x) (caddr x))
(defun fourth (x) (cadddr x))
(defun fifth (x) (car (cddddr x)))

(defun safely-delete-package (package-designator)
  (let ((package (find-package package-designator)))
    (when package
      (dolist (using-package (package-used-by-list package))
        (unuse-package package using-package))
      (delete-package package))))

(defparameter +fail-count-limit+ 20)

(defmacro return (&optional val)
  `(return-from nil ,val))

;; Minimal LOOP implementation to cover ANSI test harness needs.
;; Supports: for/in/on/from/to/below/=/repeat, while/until, when/unless,
;; do, collect, append, count, sum, always, thereis, return.
(defun %loop-kw-p (sym name)
  (and (symbolp sym) (string= (symbol-name sym) name)))

(defun %loop-clause-keyword-p (sym)
  (and (symbolp sym)
       (let ((name (symbol-name sym)))
         (or (string= name "FOR")
             (string= name "AS")
             (string= name "REPEAT")
             (string= name "WHILE")
             (string= name "UNTIL")
             (string= name "WHEN")
             (string= name "UNLESS")
             (string= name "DO")
             (string= name "COLLECT")
             (string= name "APPEND")
             (string= name "COUNT")
             (string= name "SUM")
             (string= name "ALWAYS")
             (string= name "THEREIS")
             (string= name "RETURN")
             (string= name "AND")
             (string= name "IN")
             (string= name "ON")
             (string= name "FROM")
             (string= name "TO")
             (string= name "BELOW")
             (string= name "THEN")
             (string= name "=")))))

(defun %loop-memq (x xs)
  (cond ((null xs) nil)
        ((eq x (car xs)) t)
        (t (%loop-memq x (cdr xs)))))

(defun %loop-wrap-cond (form pending-cond)
  (cond ((null pending-cond) form)
        ((eq (car pending-cond) :when) `(when ,(cadr pending-cond) ,form))
        (t `(unless ,(cadr pending-cond) ,form))))

(defun %loop-update-kind (current new)
  (if (null current) new current))

(defun %loop-collect-do-forms (tokens)
  (if (null tokens)
      (list nil nil)
      (let ((tok (car tokens)))
        (if (and (symbolp tok) (%loop-clause-keyword-p tok))
            (list nil tokens)
            (let* ((res (%loop-collect-do-forms (cdr tokens)))
                   (forms (car res))
                   (rest (cadr res)))
              (list (cons tok forms) rest))))))

(defun %loop-parse-for (tokens)
  (let ((var (car tokens))
        (rest (cdr tokens)))
    (when (null var)
      (error "loop: missing variable in for clause"))
    (let ((tok (car rest)))
      (cond
       ((%loop-kw-p tok "IN")
        (let ((expr (cadr rest))
              (tail (cddr rest))
              (cur (gensym "LOOP-LIST")))
          (list (list :in var expr cur) tail)))
       ((%loop-kw-p tok "ON")
        (let ((expr (cadr rest))
              (tail (cddr rest))
              (cur (gensym "LOOP-LIST")))
          (list (list :on var expr cur) tail)))
       ((%loop-kw-p tok "FROM")
        (let ((start-expr (cadr rest))
              (tail (cddr rest))
              (end-expr nil)
              (end-type nil))
          (when (and tail (or (%loop-kw-p (car tail) "TO")
                              (%loop-kw-p (car tail) "BELOW")))
            (setq end-type (if (%loop-kw-p (car tail) "BELOW") :below :to))
            (setq end-expr (cadr tail))
            (setq tail (cddr tail)))
          (list (list :from var start-expr end-expr end-type) tail)))
       ((%loop-kw-p tok "=")
        (let ((expr (cadr rest))
              (tail (cddr rest)))
          (when (and tail (%loop-kw-p (car tail) "THEN"))
            (setq tail (cddr tail))) ; ignore THEN form for now
          (list (list :eq var expr) tail)))
       (t
        (error "loop: malformed for clause"))))))

(defun %loop-parse-repeat (tokens)
  (let ((n (car tokens))
        (rest (cdr tokens)))
    (list (list :repeat (gensym "LOOP-REPEAT") n) rest)))

(defun %loop-parse (tokens for-specs while-tests until-tests body result-kind pending-cond acc count sum)
  (if (null tokens)
      (list for-specs while-tests until-tests body result-kind)
      (let ((tok (car tokens))
            (rest (cdr tokens)))
        (cond
         ((%loop-kw-p tok "FOR")
          (let* ((parsed (%loop-parse-for rest))
                 (spec (car parsed))
                 (tail (cadr parsed)))
            (%loop-parse tail (cons spec for-specs) while-tests until-tests body result-kind pending-cond acc count sum)))
         ((%loop-kw-p tok "AS")
          (let* ((parsed (%loop-parse-for rest))
                 (spec (car parsed))
                 (tail (cadr parsed)))
            (%loop-parse tail (cons spec for-specs) while-tests until-tests body result-kind pending-cond acc count sum)))
         ((%loop-kw-p tok "REPEAT")
          (let* ((parsed (%loop-parse-repeat rest))
                 (spec (car parsed))
                 (tail (cadr parsed)))
            (%loop-parse tail (cons spec for-specs) while-tests until-tests body result-kind pending-cond acc count sum)))
         ((%loop-kw-p tok "WHILE")
          (let ((test (car rest)))
            (%loop-parse (cdr rest) for-specs (cons test while-tests) until-tests body result-kind pending-cond acc count sum)))
         ((%loop-kw-p tok "UNTIL")
          (let ((test (car rest)))
            (%loop-parse (cdr rest) for-specs while-tests (cons test until-tests) body result-kind pending-cond acc count sum)))
         ((%loop-kw-p tok "WHEN")
          (let ((test (car rest)))
            (%loop-parse (cdr rest) for-specs while-tests until-tests body result-kind (list :when test) acc count sum)))
         ((%loop-kw-p tok "UNLESS")
          (let ((test (car rest)))
            (%loop-parse (cdr rest) for-specs while-tests until-tests body result-kind (list :unless test) acc count sum)))
         ((%loop-kw-p tok "DO")
          (let* ((parsed (%loop-collect-do-forms rest))
                 (forms (car parsed))
                 (tail (cadr parsed)))
            (if forms
                (let* ((form (if (cdr forms) `(progn ,@forms) (car forms)))
                       (wrapped (%loop-wrap-cond form pending-cond)))
                  (%loop-parse tail for-specs while-tests until-tests (cons wrapped body) result-kind nil acc count sum))
                (%loop-parse tail for-specs while-tests until-tests body result-kind nil acc count sum))))
         ((%loop-kw-p tok "COLLECT")
          (let ((expr (car rest))
                (tail (cdr rest)))
            (let* ((kind (%loop-update-kind result-kind 'collect))
                   (wrapped (%loop-wrap-cond `(setq ,acc (cons ,expr ,acc)) pending-cond)))
              (%loop-parse tail for-specs while-tests until-tests (cons wrapped body) kind nil acc count sum))))
         ((%loop-kw-p tok "APPEND")
          (let ((expr (car rest))
                (tail (cdr rest)))
            (let* ((kind (%loop-update-kind result-kind 'append))
                   (wrapped (%loop-wrap-cond `(setq ,acc (append ,acc ,expr)) pending-cond)))
              (%loop-parse tail for-specs while-tests until-tests (cons wrapped body) kind nil acc count sum))))
         ((%loop-kw-p tok "COUNT")
          (let ((expr (car rest))
                (tail (cdr rest)))
            (let* ((kind (%loop-update-kind result-kind 'count))
                   (wrapped (%loop-wrap-cond `(when ,expr (setq ,count (1+ ,count))) pending-cond)))
              (%loop-parse tail for-specs while-tests until-tests (cons wrapped body) kind nil acc count sum))))
         ((%loop-kw-p tok "SUM")
          (let ((expr (car rest))
                (tail (cdr rest)))
            (let* ((kind (%loop-update-kind result-kind 'sum))
                   (wrapped (%loop-wrap-cond `(setq ,sum (+ ,sum ,expr)) pending-cond)))
              (%loop-parse tail for-specs while-tests until-tests (cons wrapped body) kind nil acc count sum))))
         ((%loop-kw-p tok "ALWAYS")
          (let ((expr (car rest))
                (tail (cdr rest)))
            (let* ((kind (%loop-update-kind result-kind 'always))
                   (wrapped (%loop-wrap-cond `(unless ,expr (return-from nil nil)) pending-cond)))
              (%loop-parse tail for-specs while-tests until-tests (cons wrapped body) kind nil acc count sum))))
         ((%loop-kw-p tok "THEREIS")
          (let ((expr (car rest))
                (tail (cdr rest))
                (tmp (gensym "LOOP-THEREIS")))
            (let* ((kind (%loop-update-kind result-kind 'thereis))
                   (wrapped (%loop-wrap-cond `(let ((,tmp ,expr))
                                               (when ,tmp (return-from nil ,tmp)))
                                             pending-cond)))
              (%loop-parse tail for-specs while-tests until-tests (cons wrapped body) kind nil acc count sum))))
         ((%loop-kw-p tok "RETURN")
          (let ((expr (car rest))
                (tail (cdr rest)))
            (let ((wrapped (%loop-wrap-cond `(return-from nil ,expr) pending-cond)))
              (%loop-parse tail for-specs while-tests until-tests (cons wrapped body) result-kind nil acc count sum))))
         ((%loop-kw-p tok "AND")
          (%loop-parse rest for-specs while-tests until-tests body result-kind pending-cond acc count sum))
         (t
          (let ((wrapped (%loop-wrap-cond tok pending-cond)))
            (%loop-parse rest for-specs while-tests until-tests (cons wrapped body) result-kind nil acc count sum)))))))

(defun %loop-add-var (var init bound-vars init-bindings)
  (if (%loop-memq var bound-vars)
      (list bound-vars init-bindings)
      (list (cons var bound-vars) (cons (list var init) init-bindings))))

(defun %loop-build-for (specs bound-vars init-bindings pre-tests pre-assign steps end-tag)
  (if (null specs)
      (list bound-vars init-bindings pre-tests pre-assign steps)
      (let ((spec (car specs)))
        (cond
         ((eq (car spec) :in)
          (let* ((var (cadr spec))
                 (expr (caddr spec))
                 (cur (cadddr spec))
                 (res (%loop-add-var var nil bound-vars init-bindings))
                 (bound-vars2 (car res))
                 (init-bindings2 (cadr res))
                 (init-bindings3 (cons (list cur expr) init-bindings2))
                 (pre-tests2 (cons `(when (null ,cur) (go ,end-tag)) pre-tests))
                 (pre-assign2 (cons `(setq ,var (car ,cur)) pre-assign))
                 (steps2 (cons `(setq ,cur (cdr ,cur)) steps)))
            (%loop-build-for (cdr specs) bound-vars2 init-bindings3 pre-tests2 pre-assign2 steps2 end-tag)))
         ((eq (car spec) :on)
          (let* ((var (cadr spec))
                 (expr (caddr spec))
                 (cur (cadddr spec))
                 (res (%loop-add-var var nil bound-vars init-bindings))
                 (bound-vars2 (car res))
                 (init-bindings2 (cadr res))
                 (init-bindings3 (cons (list cur expr) init-bindings2))
                 (pre-tests2 (cons `(when (null ,cur) (go ,end-tag)) pre-tests))
                 (pre-assign2 (cons `(setq ,var ,cur) pre-assign))
                 (steps2 (cons `(setq ,cur (cdr ,cur)) steps)))
            (%loop-build-for (cdr specs) bound-vars2 init-bindings3 pre-tests2 pre-assign2 steps2 end-tag)))
         ((eq (car spec) :from)
          (let* ((var (cadr spec))
                 (start-expr (caddr spec))
                 (end-expr (cadddr spec))
                 (end-type (car (cddddr spec)))
                 (res (%loop-add-var var start-expr bound-vars init-bindings))
                 (bound-vars2 (car res))
                 (init-bindings2 (cadr res))
                 (pre-tests2 pre-tests)
                 (steps2 (cons `(setq ,var (1+ ,var)) steps)))
            (when end-expr
              (if (eq end-type :below)
                  (setq pre-tests2 (cons `(when (>= ,var ,end-expr) (go ,end-tag)) pre-tests2))
                (setq pre-tests2 (cons `(when (> ,var ,end-expr) (go ,end-tag)) pre-tests2))))
            (%loop-build-for (cdr specs) bound-vars2 init-bindings2 pre-tests2 pre-assign steps2 end-tag)))
         ((eq (car spec) :eq)
          (let* ((var (cadr spec))
                 (expr (caddr spec))
                 (res (%loop-add-var var nil bound-vars init-bindings))
                 (bound-vars2 (car res))
                 (init-bindings2 (cadr res))
                 (pre-assign2 (cons `(setq ,var ,expr) pre-assign)))
            (%loop-build-for (cdr specs) bound-vars2 init-bindings2 pre-tests pre-assign2 steps end-tag)))
         ((eq (car spec) :repeat)
          (let* ((counter (cadr spec))
                 (n (caddr spec))
                 (res (%loop-add-var counter 0 bound-vars init-bindings))
                 (bound-vars2 (car res))
                 (init-bindings2 (cadr res))
                 (pre-tests2 (cons `(when (>= ,counter ,n) (go ,end-tag)) pre-tests))
                 (steps2 (cons `(setq ,counter (1+ ,counter)) steps)))
            (%loop-build-for (cdr specs) bound-vars2 init-bindings2 pre-tests2 pre-assign steps2 end-tag)))
         (t
          (%loop-build-for (cdr specs) bound-vars init-bindings pre-tests pre-assign steps end-tag))))))

(defmacro loop (&rest clauses)
  (let ((start (gensym "LOOP-START"))
        (end (gensym "LOOP-END"))
        (acc (gensym "LOOP-ACC"))
        (count (gensym "LOOP-COUNT"))
        (sum (gensym "LOOP-SUM")))
    (let* ((parsed (%loop-parse clauses nil nil nil nil nil nil acc count sum))
           (for-specs (car parsed))
           (while-tests (cadr parsed))
           (until-tests (caddr parsed))
           (body (cadddr parsed))
           (result-kind (car (cddddr parsed))))
      (setq for-specs (nreverse for-specs))
      (setq while-tests (nreverse while-tests))
      (setq until-tests (nreverse until-tests))
      (setq body (nreverse body))
      (let ((init-bindings nil)
            (bound-vars nil)
            (pre-tests nil)
            (post-tests nil)
            (pre-assign nil)
            (steps nil))
        ;; Result accumulators
        (when (or (eq result-kind 'collect) (eq result-kind 'append))
          (setq init-bindings (cons (list acc nil) init-bindings)))
        (when (eq result-kind 'count)
          (setq init-bindings (cons (list count 0) init-bindings)))
        (when (eq result-kind 'sum)
          (setq init-bindings (cons (list sum 0) init-bindings)))

        (let* ((built (%loop-build-for for-specs bound-vars init-bindings pre-tests pre-assign steps end))
               (bound-vars (car built))
               (init-bindings (cadr built))
               (pre-tests (caddr built))
               (pre-assign (cadddr built))
               (steps (car (cddddr built))))
          (setq pre-tests (nreverse pre-tests))
          (setq pre-assign (nreverse pre-assign))
          (setq steps (nreverse steps))
          (setq post-tests
                (append
                 (mapcar (lambda (w) `(unless ,w (go ,end))) while-tests)
                 (mapcar (lambda (u) `(when ,u (go ,end))) until-tests)))

          (let ((return-expr
                 (cond
                  ((eq result-kind 'collect) `(nreverse ,acc))
                  ((eq result-kind 'append) acc)
                  ((eq result-kind 'sum) sum)
                  ((eq result-kind 'count) count)
                  ((eq result-kind 'always) t)
                  ((eq result-kind 'thereis) nil)
                  (t nil))))
            `(block nil
               (let ,(nreverse init-bindings)
                 (tagbody
                   ,start
                   ,@pre-tests
                   ,@pre-assign
                   ,@post-tests
                   ,@body
                   ,@steps
                   (go ,start)
                   ,end)
                 ,return-expr))))))))

(defmacro loop-finish ()
  `(return-from nil nil))

;;; Multiple values helpers
(defmacro multiple-value-list (form)
  `(multiple-value-call #'list ,form))

(defmacro nth-value (n form)
  `(nth ,n (multiple-value-list ,form)))

(defmacro multiple-value-prog1 (first-form &rest forms)
  `(let ((vals (multiple-value-list ,first-form)))
     ,@forms
     (values-list vals)))

;;; Basic stream macros (minimal)
(defmacro with-open-stream ((var stream) &rest body)
  `(let ((,var ,stream))
     (unwind-protect (progn ,@body)
       (close ,var))))

(defmacro with-open-file ((var filespec &rest options) &rest body)
  `(let ((,var (open ,filespec ,@options)))
     (unwind-protect
         (progn ,@body)
       (when ,var
         (close ,var)))))

(defmacro with-input-from-string ((var string) &rest body)
  (let ((stream (gensym "STREAM"))
        (old (gensym "OLD")))
    (if (eq var '*standard-input*)
        `(let* ((,stream (make-string-input-stream ,string))
                (,old *standard-input*))
           (setf *standard-input* ,stream)
           (unwind-protect (progn ,@body)
             (setf *standard-input* ,old)
             (close ,stream)))
        `(let* ((,stream (make-string-input-stream ,string))
                (,old *standard-input*))
           (setf *standard-input* ,stream)
           (unwind-protect (let ((,var ,stream)) ,@body)
             (setf *standard-input* ,old)
             (close ,stream))))))

(defmacro with-output-to-string ((var &optional string) &rest body)
  (declare (ignore string))
  (let ((stream (gensym "STREAM"))
        (old (gensym "OLD")))
    `(let* ((,stream (make-string-output-stream))
            (,old *standard-output*))
       (setf *standard-output* ,stream)
       (unwind-protect
           (let ((,var ,stream)) ,@body)
         (setf *standard-output* ,old))
       (get-output-stream-string ,stream))))

(defmacro with-standard-io-syntax (&rest body)
  `(progn ,@body))

;;; Reader macro placeholders (for GET-MACRO-CHARACTER)
(defun read-left-paren (stream char)
  (declare (ignore stream char))
  (error "READ-LEFT-PAREN is a reader macro placeholder"))

(defun read-right-paren (stream char)
  (declare (ignore stream char))
  (error "READ-RIGHT-PAREN is a reader macro placeholder"))

(defun read-quote (stream char)
  (declare (ignore stream char))
  (error "READ-QUOTE is a reader macro placeholder"))

(defun read-string (stream char)
  (declare (ignore stream char))
  (error "READ-STRING is a reader macro placeholder"))

(defun read-comment (stream char)
  (declare (ignore stream char))
  (error "READ-COMMENT is a reader macro placeholder"))

(defun read-backquote (stream char)
  (declare (ignore stream char))
  (error "READ-BACKQUOTE is a reader macro placeholder"))

(defun read-comma (stream char)
  (declare (ignore stream char))
  (error "READ-COMMA is a reader macro placeholder"))

(defun read-dispatch (stream char)
  (declare (ignore stream char))
  (error "READ-DISPATCH is a reader macro placeholder"))

;;; Generalized Place Handling

;; Place to store setf expander functions (Symbol Property)
;; (defconstant +setf-expander-prop+ 'setf-expander)

;;; DEFINE-SETF-EXPANDER
;;; (define-setf-expander access-fn (lambda-list) &body body)
;;; Body must return 5 values: vars, vals, store-vars, writer-form, reader-form
(defmacro define-setf-expander (access-fn lambda-list &rest body)
  `(put ',access-fn 'setf-expander
        (function (lambda (place environment)
          (declare (ignore environment)) 
          (let ((,(car lambda-list) (cdr place))) 
             ,@body)))))

(defun get-setf-expansion (place &optional environment)
  (if (symbolp place)
      (let ((store (gensym "STORE")))
        (list nil nil (list store) (list 'setq place store) place))
      (if (consp place)
          (let ((op (car place))
                (args (cdr place)))
            (let ((expander (get op 'setf-expander)))
              (if expander
                  (funcall expander place environment)
                  (let ((slot (get op 'slot-accessor)))
                    (if slot
                        (let ((temps (mapcar (lambda (x) (gensym)) args))
                              (store (gensym "STORE")))
                          (list temps
                                args
                                (list store)
                                (list 'set-slot-value (car temps) (list 'quote slot) store)
                                (cons op temps)))
                        (let ((expansion-result (macroexpand-1 place environment)))
                          (let ((expansion (car expansion-result))
                                (expanded-p (cadr expansion-result)))
                             (if expanded-p
                                 (get-setf-expansion expansion environment)
                                 (let ((temps (mapcar (lambda (x) (gensym)) args))
                                       (store (gensym "STORE")))
                                   (list temps
                                          args
                                          (list store)
                                          (append (list 'funcall (list 'function (list 'setf op)) store) temps)
                                          (cons op temps))))))))))) 
           (error "Invalid place"))))

(defmacro defsetf (access-fn &rest rest)
  (if (symbolp (car rest))
      (let ((update-fn (car rest))
            (doc (cadr rest)))
        `(define-setf-expander ,access-fn (args)
           (let ((temps (mapcar (lambda (x) (gensym)) args))
                 (store (gensym "STORE")))
             (list temps
                   args
                   (list store)

                   (cons ',update-fn (append temps (list store)))
                   (cons ',access-fn temps)))))
      (let ((lambda-list (car rest))
            (store-vars (cadr rest))
            (body (cddr rest)))
         `(define-setf-expander ,access-fn ,lambda-list
            (let ((,(car store-vars) (gensym "STORE")))
               (list nil nil (list ,(car store-vars))
                     (progn ,@body)
                     (list ',access-fn ,@lambda-list)))))))

(defsetf readtable-case set-readtable-case)

(defmacro setf (&rest p)
  (if (null p)
      nil
      (if (null (cdr p))
          `(error "SETF: Odd number of arguments")
          (let ((place (car p))
                (val (car (cdr p)))
                (rest (cdr (cdr p))))
            (let ((expansion (get-setf-expansion place)))
               (let ((vars (car expansion))
                     (vals (nth 1 expansion))
                     (store-vars (nth 2 expansion))
                     (writer (nth 3 expansion))
                     (reader (nth 4 expansion)))
                 `(let* ,(mapcar #'list vars vals)
                    (let ((,(car store-vars) ,val))
                      ,writer
                      ,@(if rest `((setf ,@rest)) nil)))))))))


(defmacro push (obj place)
  `(setf ,place (cons ,obj ,place)))

(defmacro pop (place)
  (let ((g (gensym)))
    `(let ((,g ,place))
       (setf ,place (cdr ,g))
       (car ,g))))

(defmacro incf (place &optional (delta 1))
  `(setf ,place (+ ,place ,delta)))

(defmacro decf (place &optional (delta 1))
  `(setf ,place (- ,place ,delta)))

(defsetf car rplaca)
(defsetf cdr rplacd)
;; (defsetf aref set-aref)
(defsetf slot-value set-slot-value)
(defsetf funcallable-standard-instance-access set-funcallable-standard-instance-access)
(defsetf symbol-value set)
;; (defsetf symbol-function (sym) (store)
;;   `(set-symbol-function ,sym ,store))
(defsetf get put)
(defsetf gethash set-gethash)




(defmacro assert (test-form &optional places datum &rest args)
  `(unless ,test-form
     (error (format nil "Assertion failed: ~a" ',test-form))))

(defmacro dolist ((var list &optional result) &rest body)
  (let ((lg (gensym))
        (start (gensym))
        (end (gensym)))
    `(block nil
       (let ((,lg ,list))
         (tagbody
            ,start
            (if (null ,lg) (go ,end))
            (let ((,var (car ,lg)))
               ,@body)
            (setq ,lg (cdr ,lg))
            (go ,start)
            ,end)
         ,result))))

(defmacro dotimes ((var count &optional result) &rest body)
  (let ((c (gensym))
        (start (gensym))
        (end (gensym)))
    `(block nil
       (let ((,c ,count)
             (,var 0))
         (tagbody
            ,start
            (if (>= ,var ,c) (go ,end))
            (progn ,@body)
            (setq ,var (1+ ,var))
            (go ,start)
            ,end)
         ,result))))

;;; Minimal TRACE stub
(defmacro trace (&rest specs)
  `(format t "TRACE not implemented~%"))

(defmacro time (form)
  `(sys-time-eval (lambda () ,form)))

(defmacro handler-case (form &rest cases)
  ;; Minimal stub: ignore handlers and evaluate the form.
  (declare (ignore cases))
  form)

(defmacro let* (bindings &rest body)
  (if (null bindings)
      `(progn ,@body)
      `(let (,(car bindings))
         (let* ,(cdr bindings) ,@body))))

(defmacro defconstant (name value &optional doc)
  `(defparameter ,name ,value ,doc))

(defmacro prog1 (first &rest body)
   (let ((val (gensym)))
     `(let ((,val ,first))
        (progn ,@body)
        ,val)))



;;; CLOS Macros

(defun %dc-expand-options (options)
  (if (null options)
      nil
      (let ((opt (car options)))
        (if (and (consp opt) (keywordp (car opt)))
            (let ((key (car opt))
                  (rest (cdr opt)))
              (if (null rest)
                  (%dc-expand-options (cdr options))
                  (if (null (cdr rest))
                      (cons key (cons (list 'quote (car rest))
                                      (%dc-expand-options (cdr options))))
                      (cons key (cons (list 'quote rest)
                                      (%dc-expand-options (cdr options)))))))
            (cons opt (%dc-expand-options (cdr options)))))))

(defmacro defclass (name direct-superclasses direct-slots &rest options)
  (let ((supers (if (null direct-superclasses) '(standard-object) direct-superclasses))
        (opts (%dc-expand-options options)))
    `(ensure-class-using-class (find-class ',name)
                               ',name
                               :direct-superclasses ',supers
                               :direct-slots ',direct-slots
                               ,@opts)))

(defun %dg-quote-options (options)
  (if (null options)
      nil
      (let ((opt (car options)))
        (cons (if (and (consp opt) (keywordp (car opt)))
                  (list 'quote opt)
                  opt)
              (%dg-quote-options (cdr options))))))

(defmacro defgeneric (name lambda-list &rest options)
  (let ((opts (%dg-quote-options options)))
    `(ensure-generic-function ',name :lambda-list ',lambda-list ,@opts)))

(defun %mc-pattern-list-p (lst)
  (if (null lst)
      t
      (and (or (symbolp (car lst)) (eq (car lst) '*))
           (%mc-pattern-list-p (cdr lst)))))

(defun %mc-test-p (test)
  (or (eq test '*)
      (symbolp test)
      (and (consp test) (%mc-pattern-list-p test))))

(defun %mc-group-tests-p (rest)
  (if (null rest)
      nil
      (if (keywordp (car rest))
          t
          (and (%mc-test-p (car rest))
               (%mc-group-tests-p (cdr rest))))))

(defun %mc-group-spec-p (form)
  (and (consp form)
       (symbolp (car form))
       (not (keywordp (car form)))
       (%mc-group-tests-p (cdr form))))

(defun %mc-collect-group-specs (forms acc)
  (if (and (consp forms) (%mc-group-spec-p (car forms)))
      (%mc-collect-group-specs (cdr forms) (cons (car forms) acc))
      (list (nreverse acc) forms)))

(defun %mc-split-options (forms args-spec gf-var)
  (if (null forms)
      (list args-spec gf-var nil)
      (let ((f (car forms)))
        (if (and (consp f) (keywordp (car f)))
            (let ((key (car f)))
              (cond ((eq key :arguments)
                     (%mc-split-options (cdr forms) (cdr f) gf-var))
                    ((eq key :generic-function)
                     (%mc-split-options (cdr forms) args-spec (cadr f)))
                    (t (%mc-split-options (cdr forms) args-spec gf-var))))
            (list args-spec gf-var forms)))))

(defun %mc-split-long (forms)
  (let ((group-specs nil)
        (rest forms))
    (if (and (consp rest) (consp (car rest)) (consp (caar rest)))
        (progn
          (setq group-specs (car rest))
          (setq rest (cdr rest)))
        (let ((res (%mc-collect-group-specs rest nil)))
          (setq group-specs (car res))
          (setq rest (cadr res))))
    (let ((opts (%mc-split-options rest nil nil)))
      (list group-specs (car opts) (cadr opts) (caddr opts)))))

(defun %mc-split-spec-iter (rest tests spec)
  (if (null rest)
      (list (car spec) (nreverse tests) nil)
      (if (keywordp (car rest))
          (list (car spec) (nreverse tests) rest)
          (%mc-split-spec-iter (cdr rest) (cons (car rest) tests) spec))))

(defun %mc-split-spec (spec)
  (%mc-split-spec-iter (cdr spec) nil spec))

(defun %mc-get-option (options key default)
  (if (null options)
      default
      (if (eq (car options) key)
          (cadr options)
          (%mc-get-option (cddr options) key default))))

(defun %mc-pattern-match (quals pattern)
  (cond ((eq pattern '*) t)
        ((null pattern) (null quals))
        ((consp pattern)
         (let ((p (car pattern))
               (rest (cdr pattern)))
           (cond ((eq rest '*)
                  (and (consp quals) (or (eq p '*) (eq p (car quals)))))
                 (t (and (consp quals)
                         (or (eq p '*) (eq p (car quals)))
                         (%mc-pattern-match (cdr quals) rest))))))
        (t nil)))

(defun %mc-any-pattern-match (quals patterns)
  (if (null patterns)
      nil
      (if (%mc-pattern-match quals (car patterns))
          t
          (%mc-any-pattern-match quals (cdr patterns)))))

(defun %mc-method-matches-spec-p (quals spec)
  (let* ((split (%mc-split-spec spec))
         (tests (cadr split)))
    (if (and (= (length tests) 1)
             (symbolp (car tests))
             (not (eq (car tests) '*)))
        (funcall (car tests) quals)
        (%mc-any-pattern-match quals tests))))

(defun %mc-first-matching-index (quals specs idx)
  (if (null specs)
      -1
      (if (%mc-method-matches-spec-p quals (car specs))
          idx
          (%mc-first-matching-index quals (cdr specs) (+ idx 1)))))

(defun %mc-add-to-group (groups idx method)
  (if (null groups)
      nil
      (if (= idx 0)
          (cons (append (car groups) (list method)) (cdr groups))
          (cons (car groups) (%mc-add-to-group (cdr groups) (- idx 1) method)))))

(defun %mc-init-groups (specs)
  (if (null specs) nil (cons nil (%mc-init-groups (cdr specs)))))

(defun %mc-assign-methods (methods groups specs)
  (if (null methods)
      groups
      (let* ((m (car methods))
             (quals (method-qualifiers m))
             (idx (%mc-first-matching-index quals specs 0)))
        (if (< idx 0)
            (%mc-assign-methods (cdr methods) groups specs)
            (%mc-assign-methods (cdr methods)
                                (%mc-add-to-group groups idx m)
                                specs)))))

(defun %mc-apply-group-options (groups specs)
  (if (null specs)
      nil
      (let* ((spec (car specs))
             (split (%mc-split-spec spec))
             (options (caddr split))
             (group (car groups))
             (order (%mc-get-option options :order :most-specific-first))
             (required (%mc-get-option options :required nil))
             (group2 (if (eq order :most-specific-last) (reverse group) group)))
        (if (and required (null group2))
            (error "Required method group missing"))
        (cons group2 (%mc-apply-group-options (cdr groups) (cdr specs))))))

(defun %mc-group-methods (methods specs)
  (%mc-apply-group-options
   (%mc-assign-methods methods (%mc-init-groups specs) specs)
   specs))

(defun %mc-group-bindings (groups-sym vars)
  (if (null vars)
      nil
      (cons (list (car vars) (list 'car groups-sym))
            (cons (list groups-sym (list 'cdr groups-sym))
                  (%mc-group-bindings groups-sym (cdr vars))))))

(defun %mc-wrap-long-body (body params args-spec gf-var)
  (let ((inner `(progn ,@body)))
    (if args-spec
        (setq inner `(apply (function (lambda ,args-spec ,inner)) args)))
    (if params
        (setq inner `(apply (function (lambda ,params ,inner)) options)))
    (if gf-var
        (setq inner `(let ((,gf-var gf)) ,inner)))
    inner))

(defmacro define-method-combination (name &rest rest)
  (if (and rest (or (consp (car rest)) (null (car rest))) (not (keywordp (car rest))))
      (let* ((params (car rest))
             (parts (%mc-split-long (cdr rest)))
             (group-specs (car parts))
             (args-spec (cadr parts))
             (gf-var (caddr parts))
             (body (cadddr parts))
             (group-vars (mapcar #'car group-specs))
             (groups-sym (gensym))
             (bindings (%mc-group-bindings groups-sym group-vars))
             (wrapped (%mc-wrap-long-body body params args-spec gf-var)))
        `(register-method-combination ',name
           :type :long
           :expander
           (function
            (lambda (gf methods options args)
              (let* ((,groups-sym (%mc-group-methods methods ',group-specs))
                     ,@bindings)
                ,wrapped)))))
      (let* ((op (%mc-get-option rest :operator name))
             (id (%mc-get-option rest :identity-with-one-argument nil)))
        `(register-method-combination ',name
           :type :operator
           :operator ',op
           :identity-with-one-argument ,id))))

(defmacro make-method (form)
  (let ((args (gensym)))
    `(sys-make-method
      (function (lambda (&rest ,args) ,form)))))

(defparameter *use-make-method-lambda* nil)

(defun parse-defmethod-qualifiers (args qualifiers)
  (if (and (consp args) (symbolp (car args)) (not (null (car args))))
      (if (listp (car args))
          (list qualifiers args) ; Done, return (qualifiers rest)
          (parse-defmethod-qualifiers (cdr args) (cons (car args) qualifiers)))
      (list qualifiers args)))

(defun parse-defmethod-lambda-list (args clean-ll specs)
  (if (null args)
      (list (nreverse clean-ll) (nreverse specs))
      (let ((arg (car args)))
        (if (or (eq arg '&optional) (eq arg '&rest) (eq arg '&key) (eq arg '&aux))
            (list (append (nreverse clean-ll) args) (nreverse specs))
            (if (consp arg)
                (parse-defmethod-lambda-list (cdr args) 
                                             (cons (car arg) clean-ll) 
                                             (cons (cadr arg) specs))
                (parse-defmethod-lambda-list (cdr args) 
                                             (cons arg clean-ll) 
                                             (cons t specs)))))))

(defmacro defmethod (name &rest args)
  (let* ((parse-result (parse-defmethod-qualifiers args nil))
         (qualifiers (nreverse (car parse-result)))
         (rest (cadr parse-result))
         (ll (car rest))
         (body (cdr rest)))
    ;; Parse lambda list to extract specializers
    (let ((ll-result (parse-defmethod-lambda-list ll nil nil)))
      (let ((clean-ll (car ll-result))
            (specs (cadr ll-result)))
        `(let* ((gf (if (fboundp ',name)
                        (symbol-function ',name)
                        (ensure-generic-function ',name :lambda-list ',clean-ll)))
                (fn (function (lambda ,clean-ll ,@body))))
           (ensure-method gf
                          :lambda-list ',clean-ll
                          :qualifiers ',qualifiers
                          :specializers ',specs
                          :body (if (and *use-make-method-lambda*
                                         (generic-function-methods
                                          (symbol-function 'make-method-lambda)))
                                    (make-method-lambda gf nil fn nil)
                                    fn)))))))

(defgeneric allocate-instance (class &rest initargs))
(defgeneric initialize-instance (instance &rest initargs))
(defgeneric shared-initialize (instance slot-names &rest initargs))
(defgeneric make-instance (class &rest initargs))
(defgeneric ensure-class-using-class (class name &rest initargs))
(defgeneric validate-superclass (class superclass))
(defgeneric finalize-inheritance (class))
(defgeneric reinitialize-instance (instance &rest initargs))
(defgeneric change-class (instance new-class &rest initargs))
(defgeneric update-instance-for-redefined-class (instance added discarded plist &rest initargs))
(defgeneric slot-missing (class instance slot-name operation &optional new-value))
(defgeneric slot-unbound (class instance slot-name))
(defgeneric make-direct-slot-definition (class &rest initargs))
(defgeneric make-effective-slot-definition (class &rest initargs))
(defgeneric compute-discriminating-function (gf))
(defgeneric compute-effective-method (gf method-combination methods))
(defgeneric compute-effective-method-function (gf effective-method))
(defgeneric method-function (method))
(defgeneric make-method-lambda (gf method lambda-expression env))
(defgeneric generic-function-argument-precedence-order (gf))
(defgeneric class-direct-methods (class))
(defgeneric class-direct-generic-functions (class))
(defgeneric specializer-direct-methods (specializer))
(defgeneric specializer-direct-generic-functions (specializer))
(defgeneric add-dependent (metaobject dependent))
(defgeneric remove-dependent (metaobject dependent))
(defgeneric map-dependents (metaobject function))
(defgeneric update-dependent (metaobject dependent &rest initargs))

(defun ensure-class (name &rest initargs)
  (apply #'ensure-class-using-class (find-class name) name initargs))

(defmethod allocate-instance ((class standard-class) &rest initargs)
  (sys-allocate-instance class))

(defmethod initialize-instance ((instance standard-object) &rest initargs)
  (if (null initargs)
      (shared-initialize instance t)
      (apply #'shared-initialize instance t initargs)))

(defmethod shared-initialize ((instance standard-object) slot-names &rest initargs)
  (apply #'sys-shared-initialize-prim instance slot-names initargs))

(defmethod ensure-class-using-class ((class t) name &rest initargs)
  (apply #'sys-ensure-class name initargs))

(defmethod validate-superclass ((class t) (superclass t))
  t)

(defmethod finalize-inheritance ((class standard-class))
  (sys-finalize-inheritance class))

(defmethod reinitialize-instance ((instance standard-object) &rest initargs)
  (apply #'sys-reinitialize-instance instance initargs))

(defmethod change-class ((instance standard-object) (new-class standard-class) &rest initargs)
  (apply #'sys-change-class instance new-class initargs))

(defmethod change-class ((instance standard-object) (new-class symbol) &rest initargs)
  (apply #'change-class instance (find-class new-class) initargs))

(defmethod update-instance-for-redefined-class
  ((instance standard-object) added discarded plist &rest initargs)
  instance)

(defmethod slot-missing ((class standard-class) instance slot-name operation &optional new-value)
  (error "Slot missing"))

(defmethod slot-unbound ((class standard-class) instance slot-name)
  (error "Slot unbound"))

(defmethod make-direct-slot-definition ((class standard-class) &rest initargs)
  (apply #'sys-make-direct-slot-definition class initargs))

(defmethod make-effective-slot-definition ((class standard-class) &rest initargs)
  (apply #'sys-make-effective-slot-definition class initargs))

(defmethod compute-discriminating-function ((gf standard-generic-function))
  (function (lambda (&rest args)
              (sys-dispatch-generic gf args))))

(defmethod compute-effective-method ((gf standard-generic-function) method-combination methods)
  methods)

(defmethod compute-effective-method-function ((gf standard-generic-function) effective-method)
  (function (lambda (&rest args)
              (sys-apply-effective-method gf effective-method args))))

(defmethod method-function ((method standard-method))
  (method-body method))

(defmethod make-method-lambda ((gf standard-generic-function) method lambda-expression env)
  lambda-expression)

(defgeneric eql-specializer-object (specializer))
(defmethod eql-specializer-object ((specializer eql-specializer))
  (sys-eql-specializer-object specializer))

(defmethod generic-function-argument-precedence-order ((gf standard-generic-function))
  (sys-generic-function-argument-precedence-order gf))

(defmethod class-direct-methods ((class standard-class))
  (sys-class-direct-methods class))

(defmethod class-direct-generic-functions ((class standard-class))
  (sys-class-direct-generic-functions class))

(defmethod specializer-direct-methods ((specializer standard-class))
  (sys-specializer-direct-methods specializer))

(defmethod specializer-direct-methods ((specializer eql-specializer))
  (sys-specializer-direct-methods specializer))

(defmethod specializer-direct-generic-functions ((specializer standard-class))
  (sys-specializer-direct-generic-functions specializer))

(defmethod specializer-direct-generic-functions ((specializer eql-specializer))
  (sys-specializer-direct-generic-functions specializer))

(defmethod add-dependent ((metaobject standard-class) dependent)
  (sys-add-dependent metaobject dependent))

(defmethod add-dependent ((metaobject standard-generic-function) dependent)
  (sys-add-dependent metaobject dependent))

(defmethod remove-dependent ((metaobject standard-class) dependent)
  (sys-remove-dependent metaobject dependent))

(defmethod remove-dependent ((metaobject standard-generic-function) dependent)
  (sys-remove-dependent metaobject dependent))

(defmethod map-dependents ((metaobject standard-class) function)
  (sys-map-dependents metaobject function))

(defmethod map-dependents ((metaobject standard-generic-function) function)
  (sys-map-dependents metaobject function))

(defmethod update-dependent ((metaobject standard-class) dependent &rest initargs)
  nil)

(defmethod update-dependent ((metaobject standard-generic-function) dependent &rest initargs)
  nil)

(setf *use-make-method-lambda* t)

(defmethod make-instance ((class standard-class) &rest initargs)
  (if (null initargs)
      (let ((instance (allocate-instance class)))
        (initialize-instance instance)
        instance)
      (let ((instance (apply #'allocate-instance class initargs)))
        (apply #'initialize-instance instance initargs)
        instance)))

(defmethod make-instance ((class symbol) &rest initargs)
  (if (null initargs)
      (make-instance (find-class class))
      (apply #'make-instance (find-class class) initargs)))

(defclass point () (x y))

;;; Export CL-level macros/functions defined in this file
(export
 '(when unless or and cond declaim defstruct in-package defpackage with-package-iterator
   do-symbols do-external-symbols do-all-symbols return loop loop-finish multiple-value-list
   nth-value multiple-value-prog1 with-open-stream with-input-from-string
   with-output-to-string with-standard-io-syntax define-setf-expander defsetf setf
   push pop incf decf assert dolist dotimes trace time handler-case let* defconstant prog1
   defclass defgeneric define-method-combination make-method defmethod
   not null mapcar some append reverse nreverse caar cadr cdar cddr caaar caadr
   cadar caddr cdaar cdadr cddar cdddr caaaar caaadr caadar caaddr cadaar cadadr
   caddar cadddr cdaaar cdaadr cdadar cdaddr cddaar cddadr cdddar cddddr first
   second third fourth fifth get-setf-expansion notnot notnot-mv notnot-mv-fn
   not-mv not-mv-fn eqt eqlt equalt equalpt safely-delete-package
   +fail-count-limit+))

;; REPL convenience (no-op in non-interactive runs)
(defun quit (&optional code)
  nil)
