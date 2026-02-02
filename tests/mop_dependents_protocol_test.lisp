(format t "Starting MOP Dependents Protocol Test...~%")

(defclass dep-class () ())
(defgeneric dep-gf (x))

(defparameter *map-deps* nil)
(defparameter *class-updates* nil)
(defparameter *gf-updates* nil)

(defmethod update-dependent ((class standard-class) (dep symbol) &rest initargs)
  (setf *class-updates* (cons (list dep initargs) *class-updates*)))

(defmethod update-dependent ((gf standard-generic-function) (dep symbol) &rest initargs)
  (setf *gf-updates* (cons initargs *gf-updates*)))

(let ((cls (find-class 'dep-class)))
  (add-dependent cls 'alpha)
  (add-dependent cls 'beta)
  (add-dependent cls 'alpha)
  (map-dependents cls (lambda (d) (setf *map-deps* (cons d *map-deps*))))
  (if (= (length *map-deps*) 2)
      (format t "MAP-DEPENDENTS adds unique dependents OK~%")
      (format t "MAP-DEPENDENTS adds unique dependents FAIL: ~A~%" *map-deps*))
  (remove-dependent cls 'alpha)
  (setf *map-deps* nil)
  (map-dependents cls (lambda (d) (setf *map-deps* (cons d *map-deps*))))
  (if (= (length *map-deps*) 1)
      (format t "REMOVE-DEPENDENT OK~%")
      (format t "REMOVE-DEPENDENT FAIL: ~A~%" *map-deps*))
  (ensure-class 'dep-class :direct-slots '((extra)))
  (if *class-updates*
      (format t "CLASS UPDATE-DEPENDENT OK~%")
      (format t "CLASS UPDATE-DEPENDENT FAIL~%")))

(add-dependent (symbol-function 'dep-gf) 'gf-watch)
(defmethod dep-gf ((x integer)) :int)

(if (and *gf-updates* (eq (car (car *gf-updates*)) :add-method))
    (format t "GF UPDATE-DEPENDENT add-method OK~%")
    (format t "GF UPDATE-DEPENDENT add-method FAIL: ~A~%" *gf-updates*))
