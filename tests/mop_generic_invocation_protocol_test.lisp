(format t "Starting MOP Generic Invocation Protocol Test...~%")

(defparameter *cdf-count* 0)
(defparameter *cef-count* 0)

(defclass apo-a () ())
(defclass apo-a1 (apo-a) ())
(defclass apo-b () ())
(defclass apo-b1 (apo-b) ())

(defgeneric pick (x y) (:argument-precedence-order (y x)))

(defmethod pick ((x apo-a1) (y apo-b)) 'x)
(defmethod pick ((x apo-a) (y apo-b1)) 'y)

(let ((gf (symbol-function 'pick)))
  (if (eq (class-of gf) (find-class 'standard-generic-function))
      (format t "GENERIC-FUNCTION class-of OK~%")
      (format t "GENERIC-FUNCTION class-of FAIL: ~A~%" gf))
  (format t "PICK methods: ~A~%" (length (generic-function-methods gf))))

(let ((gf (symbol-function 'compute-effective-method-function)))
  (format t "CEF name: ~A~%" (generic-function-name gf))
  (format t "COMPUTE-EFFECTIVE-METHOD-FUNCTION methods: ~A~%"
          (length (generic-function-methods gf)))
  (let ((m (car (generic-function-methods gf))))
    (format t "CEF method specializers: ~A~%" (method-specializers m))))

(defmethod compute-discriminating-function :before ((gf standard-generic-function))
  (if (eq (generic-function-name gf) 'pick)
      (setf *cdf-count* (+ *cdf-count* 1))))

(defmethod compute-effective-method-function :before
  ((gf standard-generic-function) effective-method)
  (if (eq (generic-function-name gf) 'pick)
      (setf *cef-count* (+ *cef-count* 1))))

(let* ((a (make-instance 'apo-a1))
       (b (make-instance 'apo-b1))
       (args (list a b)))
  (format t "Applicable methods: ~A~%"
          (compute-applicable-methods (symbol-function 'pick) args))
  (let ((sys-res (sys-dispatch-generic (symbol-function 'pick) args)))
    (format t "SYS-DISPATCH-GENERIC res: ~A~%" sys-res))
  (let ((res (pick a b)))
    (if (eq res 'y)
        (format t "ARGUMENT-PRECEDENCE-ORDER OK~%")
        (format t "ARGUMENT-PRECEDENCE-ORDER FAIL: ~A~%" res)))
  ;; Call again to ensure caching
  (pick a b))

(if (= *cdf-count* 1)
    (format t "COMPUTE-DISCRIMINATING-FUNCTION cache OK~%")
    (format t "COMPUTE-DISCRIMINATING-FUNCTION cache FAIL: ~A~%" *cdf-count*))

(if (= *cef-count* 1)
    (format t "COMPUTE-EFFECTIVE-METHOD-FUNCTION cache OK~%")
    (format t "COMPUTE-EFFECTIVE-METHOD-FUNCTION cache FAIL: ~A~%" *cef-count*))

(let* ((gf (symbol-function 'pick))
       (apo (generic-function-argument-precedence-order gf)))
  (if (and apo (eq (car apo) 'y) (eq (cadr apo) 'x))
      (format t "ARGUMENT-PRECEDENCE-ORDER accessor OK~%")
      (format t "ARGUMENT-PRECEDENCE-ORDER accessor FAIL: ~A~%" apo)))

(let* ((gf (symbol-function 'pick))
       (methods (generic-function-methods gf))
       (target nil))
  (dolist (m methods)
    (let ((specs (method-specializers m)))
      (if (and specs (eq (car specs) (find-class 'apo-a1)))
          (setq target m))))
  (let* ((fn (method-function target))
         (res (apply fn (list (make-instance 'apo-a1) (make-instance 'apo-b)))))
    (if (eq res 'x)
        (format t "METHOD-FUNCTION OK~%")
        (format t "METHOD-FUNCTION FAIL: ~A~%" res))))

(let* ((gf (symbol-function 'pick))
       (df (compute-discriminating-function gf))
       (res (apply df (list (make-instance 'apo-a1) (make-instance 'apo-b1)))))
  (if (eq res 'y)
      (format t "COMPUTE-DISCRIMINATING-FUNCTION returns function OK~%")
      (format t "COMPUTE-DISCRIMINATING-FUNCTION returns function FAIL: ~A~%" res)))
