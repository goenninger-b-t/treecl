(format t "Starting MOP Introspection Extras Test...~%")

(defclass cm-a () ())
(defclass cm-b () ())

(defgeneric gf1 (x))
(defmethod gf1 ((x cm-a)) :a)

(defgeneric gf2 (x y))
(defmethod gf2 ((x cm-a) (y cm-b)) :ab)
(defmethod gf2 ((x cm-b) (y cm-a)) :ba)

(defgeneric gf3 (x))
(defmethod gf3 ((x (eql 5))) :eql)

(defun list-contains (item lst)
  (if (null lst)
      nil
      (if (eq item (car lst))
          t
          (list-contains item (cdr lst)))))

(defun method-has-specializer (method spec)
  (list-contains spec (method-specializers method)))

(let* ((a-class (find-class 'cm-a))
       (methods (class-direct-methods a-class)))
  (let ((ok t))
    (dolist (m methods)
      (unless (method-has-specializer m a-class)
        (setf ok nil)))
    (if ok
        (format t "CLASS-DIRECT-METHODS OK~%")
        (format t "CLASS-DIRECT-METHODS FAIL: ~A~%" methods)))
  (if (= (length methods) 3)
      (format t "CLASS-DIRECT-METHODS count OK~%")
      (format t "CLASS-DIRECT-METHODS count FAIL: ~A~%" (length methods))))

(let* ((a-class (find-class 'cm-a))
       (gfs (class-direct-generic-functions a-class))
       (gf1-obj (symbol-function 'gf1))
       (gf2-obj (symbol-function 'gf2))
       (gf3-obj (symbol-function 'gf3)))
  (if (and (list-contains gf1-obj gfs)
           (list-contains gf2-obj gfs)
           (not (list-contains gf3-obj gfs)))
      (format t "CLASS-DIRECT-GENERIC-FUNCTIONS OK~%")
      (format t "CLASS-DIRECT-GENERIC-FUNCTIONS FAIL: ~A~%" gfs)))

(let* ((eql-spec (intern-eql-specializer 5))
       (methods (specializer-direct-methods eql-spec)))
  (if (and (= (length methods) 1)
           (method-has-specializer (car methods) eql-spec))
      (format t "SPECIALIZER-DIRECT-METHODS OK~%")
      (format t "SPECIALIZER-DIRECT-METHODS FAIL: ~A~%" methods)))

(let* ((eql-spec (intern-eql-specializer 5))
       (gfs (specializer-direct-generic-functions eql-spec))
       (gf3-obj (symbol-function 'gf3)))
  (if (and (= (length gfs) 1)
           (list-contains gf3-obj gfs))
      (format t "SPECIALIZER-DIRECT-GENERIC-FUNCTIONS OK~%")
      (format t "SPECIALIZER-DIRECT-GENERIC-FUNCTIONS FAIL: ~A~%" gfs)))
