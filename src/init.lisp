
;;; TreeCL Standard Library (Prelude)

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




(defun not (x) (if x nil t))
(defun null (x) (if x nil t))

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

(defun member (item list)
  (if (null list)
      nil
      (if (eql item (car list))
          list
          (member item (cdr list)))))

(defun eql (x y)
  (eq x y)) ;;; primitive eq handles everything for now? or need primitive eql


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

(defmacro return (&optional val)
  `(return-from nil ,val))

(defmacro loop (&rest body)
  ;; Minimal infinite loop used in simplistic code
  ;; Real loop is complex
  (let ((g (gensym)))
    `(block nil (tagbody ,g (progn ,@body) (go ,g)))))

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
            (progn
               (list (append (nreverse clean-ll) args) (nreverse specs)))
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

;; REPL convenience (no-op in non-interactive runs)
(defun quit (&optional code)
  nil)
