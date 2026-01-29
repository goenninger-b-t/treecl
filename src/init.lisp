
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
               (if ,gp ,gp (or ,@optimize (cdr args))))))))

(defmacro and (&rest args)
  (if (null args)
      t
      (if (null (cdr args))
          (car args)
          `(if ,(car args) (and ,@(cdr args)) nil))))

(defmacro return (val)
  `(return-from nil ,val))

(defmacro loop (&rest body)
  ;; Minimal infinite loop used in simplistic code
  ;; Real loop is complex
  (let ((g (gensym)))
    `(block nil (tagbody ,g (progn ,@body) (go ,g)))))

(defmacro setf (place value)
  (if (symbolp place)
      `(setq ,place ,value)
      (if (consp place)
          (let ((op (car place))
                (args (cdr place)))
            (format t "DEBUG-SETF op: ~A (eq op 'get): ~A~%" op (eq op 'get))
            (if (eq op 'aref)
                `(set-aref ,(car args) ,@(cdr args) ,value)
                (if (eq op 'slot-value)
                    `(set-slot-value ,(car args) ,@(cdr args) ,value)
                    (if (eq op 'get)
                        `(put ,(car args) ,(car (cdr args)) ,value)
                        (if (eq op 'car) 
                             ;; Warning: Cons mutation not fully supported?
                             `(error "SETF CAR not implemented")
                             (if (eq op 'cdr)
                                 `(error "SETF CDR not implemented")
                                 `(error ,(format nil "Unknown SETF place: ~a" op))))))))
           `(error "Invalid SETF place"))))

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


