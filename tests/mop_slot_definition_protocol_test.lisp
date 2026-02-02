(format t "Starting MOP Slot Definition Protocol Test...~%")

(defun make-const-42 () 42)

(defclass unbound-test () (a))

(defmethod slot-unbound ((class standard-class) instance slot-name)
  :unbound)

(let ((obj (make-instance 'unbound-test)))
  (if (eq (slot-value obj 'a) :unbound)
      (format t "SLOT-UNBOUND hook OK~%")
      (format t "SLOT-UNBOUND hook FAIL~%")))

(defclass missing-test () ())

(defmethod slot-missing ((class standard-class) instance slot-name operation &optional new-value)
  (if (eq operation 'set-slot-value)
      new-value
      :missing))

(let ((obj (make-instance 'missing-test)))
  (if (eq (slot-value obj 'nope) :missing)
      (format t "SLOT-MISSING (slot-value) OK~%")
      (format t "SLOT-MISSING (slot-value) FAIL~%"))
  (if (= (set-slot-value obj 'nope 9) 9)
      (format t "SLOT-MISSING (set-slot-value) OK~%")
      (format t "SLOT-MISSING (set-slot-value) FAIL~%")))

(defclass initfun-test ()
  ((x :initfunction (function make-const-42) :type integer)))

(let ((obj (make-instance 'initfun-test)))
  (if (= (slot-value obj 'x) 42)
      (format t "INITFUNCTION default OK~%")
      (format t "INITFUNCTION default FAIL~%")))

(let* ((d (make-direct-slot-definition (find-class 'standard-class)
                                       :name 'foo
                                       :initform 7
                                       :initargs '(:foo)))
       (e (make-effective-slot-definition (find-class 'standard-class)
                                          :name 'bar
                                          :initform 8
                                          :initargs '(:bar)
                                          :location 0)))
  (if (eq (class-of d) (find-class 'standard-direct-slot-definition))
      (format t "MAKE-DIRECT-SLOT-DEFINITION class OK~%")
      (format t "MAKE-DIRECT-SLOT-DEFINITION class FAIL~%"))
  (if (eq (slot-definition-name d) 'foo)
      (format t "MAKE-DIRECT-SLOT-DEFINITION name OK~%")
      (format t "MAKE-DIRECT-SLOT-DEFINITION name FAIL~%"))
  (if (and (slot-definition-initargs d)
           (eq (car (slot-definition-initargs d)) :foo))
      (format t "MAKE-DIRECT-SLOT-DEFINITION initargs OK~%")
      (format t "MAKE-DIRECT-SLOT-DEFINITION initargs FAIL~%"))
  (if (eq (class-of e) (find-class 'standard-effective-slot-definition))
      (format t "MAKE-EFFECTIVE-SLOT-DEFINITION class OK~%")
      (format t "MAKE-EFFECTIVE-SLOT-DEFINITION class FAIL~%"))
  (if (= (slot-definition-location e) 0)
      (format t "MAKE-EFFECTIVE-SLOT-DEFINITION location OK~%")
      (format t "MAKE-EFFECTIVE-SLOT-DEFINITION location FAIL~%")))
