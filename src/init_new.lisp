
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

(defmacro return (val)
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
                                    (cons op temps))))))))) 
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
(defsetf symbol-value set)
;; (defsetf symbol-function (sym) (store)
;;   `(set-symbol-function ,sym ,store))
;; (defsetf get (sym indicator &optional default) (store)
;;   `(put ,sym ,indicator ,store))




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

(defmacro defclass (name direct-superclasses direct-slots &rest options)
  ;; Simplified DEFCLASS: options ignored for now
  (let ((supers (if (null direct-superclasses) '(standard-object) direct-superclasses)))
    `(ensure-class ',name 
                   :direct-superclasses ',supers 
                   :direct-slots ',direct-slots)))

(defmacro defgeneric (name lambda-list &rest options)
  `(ensure-generic-function ',name :lambda-list ',lambda-list))

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
  (let ((parse-result (parse-defmethod-qualifiers args nil)))
    (let ((qualifiers (nreverse (car parse-result)))
          (rest (cadr parse-result)))
    
    (let ((ll (car rest)))
      (setq body (cdr rest))
      ;; Parse lambda list to extract specializers
      (let ((ll-result (parse-defmethod-lambda-list ll nil nil)))
        (let ((clean-ll (car ll-result))
              (specs (cadr ll-result)))
        
        `(ensure-method ',name 
                        :lambda-list ',clean-ll 
                        :qualifiers ',qualifiers 
                        :specializers ',specs 
                        :body (function (lambda ,clean-ll ,@body)))))))))

(print "Defining allocate-instance generic")
(defgeneric allocate-instance (class &rest initargs))
(print "Defining initialize-instance generic")
(defgeneric initialize-instance (instance &rest initargs))
(print "Defining shared-initialize generic")
(defgeneric shared-initialize (instance slot-names &rest initargs))
(print "Defining make-instance generic")
(defgeneric make-instance (class &rest initargs))

(print "Defining method allocate-instance")
(defmethod allocate-instance ((class standard-class) &rest initargs)
  (sys-allocate-instance class))

(print "Defining method initialize-instance")
(defmethod initialize-instance ((instance standard-object) &rest initargs)
  (apply #'shared-initialize instance t initargs))

(print "Defining method shared-initialize")
(defmethod shared-initialize ((instance standard-object) slot-names &rest initargs)
  (apply #'sys-shared-initialize-prim instance slot-names initargs))

(print "Defining method make-instance (standard-class)")
(defmethod make-instance ((class standard-class) &rest initargs)
  (let ((instance (apply #'allocate-instance class initargs)))
    (apply #'initialize-instance instance initargs)
    instance))

(print "Defining method make-instance (symbol)")
(defmethod make-instance ((class symbol) &rest initargs)
  (apply #'make-instance (find-class class) initargs))

(defclass point () (x y))

