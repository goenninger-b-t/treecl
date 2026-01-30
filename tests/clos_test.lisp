
(format t "Testing CLOS support...~%")

;; Check if DEFCLASS is defined
(if (fboundp 'defclass)
    (format t "DEFCLASS is present.~%")
    (format t "DEFCLASS is MISSING.~%"))

;; Try to define a class if macro missing, this will fail read/eval if not handled, 
;; so we wrap in ignore-errors or just let it crash to prove the point.
;; Actually, if it's not defined, the reader might parse it as a function call, 
;; and eval will fail with "Undefined function DEFCLASS".

;; (ignore-errors
;;   (eval '(defclass point () ((x) (y)))))

(if (fboundp 'ensure-class)
    (format t "ENSURE-CLASS is present.~%")
    (format t "ENSURE-CLASS is MISSING.~%"))

(if (fboundp 'ensure-generic-function)
    (format t "ENSURE-GENERIC-FUNCTION is present.~%")
    (format t "ENSURE-GENERIC-FUNCTION is MISSING.~%"))

(if (fboundp 'ensure-method)
    (format t "ENSURE-METHOD is present.~%")
    (format t "ENSURE-METHOD is MISSING.~%"))

;; Test DEFCLASS
(format t "Defining class POINT...~%")
(defclass point () ((x) (y)))

(if (find-class 'point)
    (format t "Class POINT defined.~%")
    (format t "Class POINT NOT defined.~%"))

;; Test MAKE-INSTANCE and SLOT-VALUE
(format t "Creating instance...~%")
(defparameter p1 (make-instance 'point))

(format t "Setting slots...~%")
(setf (slot-value p1 'x) 10)
;; Test explicit set-slot-value to debug primitive invocation
(format t "Testing explicit SET-SLOT-VALUE...~%")
(set-slot-value p1 'x 10)
(format t "Explicit set p.x = ~a~%" (slot-value p1 'x))

;; Check expansion
(format t "Macro expansion of (setf (slot-value p1 'x) 10):~%~A~%" (macroexpand-1 '(setf (slot-value p1 'x) 10)))
(format t "~%")

(setf (slot-value p1 'y) 20)
(format t "p1.x = ~A~%" (slot-value p1 'x))
(format t "p1.y = ~A~%" (slot-value p1 'y))

(if (= (slot-value p1 'x) 10)
    (format t "Slot access OK.~%")
    (format t "Slot access FAILED.~%"))

;; Test Inheritance
(format t "Defining class P3D...~%")
(defclass p3d (point) ((z)))

(defparameter p2 (make-instance 'p3d))
(setf (slot-value p2 'x) 1.0)
(setf (slot-value p2 'z) 3.0)

(format t "p2.x (inherited) = ~A~%" (slot-value p2 'x))
(format t "p2.z = ~A~%" (slot-value p2 'z))

;; Test Generic Functions
(format t "Defining generic MAGNITUDE...~%")
(defgeneric magnitude (obj))

(format t "Defining method MAGNITUDE for POINT...~%")
(defmethod magnitude ((obj point))
  (let ((x (slot-value obj 'x))
        (y (slot-value obj 'y)))
    (+ x y))) ;; Simple sum for test, sqrt is expensive/missing?

(format t "Calling MAGNITUDE on p1...~%")
(defparameter mag1 (magnitude p1))
(format t "Magnitude(p1) = ~A~%" mag1)

(if (= mag1 30)
    (format t "Method dispatch OK.~%")
    (format t "Method dispatch FAILED.~%"))

;; Test method on subclass
(format t "Defining method MAGNITUDE for P3D...~%")
(defmethod magnitude ((obj p3d))
  (+ (slot-value obj 'z) (call-next-method))) ;; Wait, call-next-method not impl?
  ;; I haven't implemented call-next-method.
  ;; Standard CLOS allows primary methods to shadow.
  ;; For this test, I will just reimplement logic or use primary method semantics.
  ;; If I define primary method on P3D, it overrides POINT.
  ;; To use next method, I need `call-next-method` primitive or macro magic.
  ;; I haven't implemented that yet.
  
  ;; Simpler test: Override completely.
(defmethod magnitude ((obj p3d))
    (+ 1000 (slot-value obj 'z)))

(defparameter mag2 (magnitude p2))
(format t "Magnitude(p2) = ~A~%" mag2)

(if (= mag2 1003.0)
   (format t "Method override OK.~%")
   (format t "Method override FAILED.~%"))

(quit)
