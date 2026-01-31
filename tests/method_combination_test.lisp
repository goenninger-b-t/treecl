(format t "Testing standard method combination...~%")

(defparameter *log* nil)

(defclass base () ())
(defclass sub (base) ())

(defgeneric combine (obj))

;; Primary methods
(defmethod combine ((o base))
  (setf *log* (cons 'primary-base *log*))
  'base)

(defmethod combine ((o sub))
  (setf *log* (cons 'primary-sub *log*))
  (call-next-method))

;; Before methods
(defmethod combine :before ((o base))
  (setf *log* (cons 'before-base *log*)))

(defmethod combine :before ((o sub))
  (setf *log* (cons 'before-sub *log*)))

;; After methods
(defmethod combine :after ((o base))
  (setf *log* (cons 'after-base *log*)))

(defmethod combine :after ((o sub))
  (setf *log* (cons 'after-sub *log*)))

;; Around method
(defmethod combine :around ((o sub))
  (setf *log* (cons 'around-sub *log*))
  (call-next-method))

(defparameter inst (make-instance 'sub))
(combine inst)

;; Expected execution order (reverse, since we cons onto *log*)
(defparameter expected
  '(after-sub after-base primary-base primary-sub before-base before-sub around-sub))

(if (equal *log* expected)
    (format t "Standard method combination PASS~%")
    (format t "Standard method combination FAIL: ~A~%" *log*))
