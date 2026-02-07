(format t "Starting MOP Funcallable Instances Test...~%")

(let ((fsc (find-class 'funcallable-standard-class))
      (fso (find-class 'funcallable-standard-object)))
  (if (and fsc fso)
      (format t "FUNCALLABLE classes exist OK~%")
      (format t "FUNCALLABLE classes exist FAIL~%"))
  (if (eq (class-of fso) fsc)
      (format t "FUNCALLABLE-STANDARD-OBJECT class-of OK~%")
      (format t "FUNCALLABLE-STANDARD-OBJECT class-of FAIL~%")))

(defclass functor ()
  ((val :initform 0))
  (:metaclass funcallable-standard-class))

(let* ((cls (find-class 'functor))
       (supers (class-direct-superclasses cls)))
  (if (and supers (eq (car supers) (find-class 'funcallable-standard-object)))
      (format t "FUNCALLABLE default superclass OK~%")
      (format t "FUNCALLABLE default superclass FAIL: ~A~%" supers)))

(let ((inst (make-instance 'functor)))
  (set-funcallable-instance-function
   inst
   (function (lambda (x) (+ x 10))))
  (let ((res (funcall inst 5)))
    (if (= res 15)
        (format t "FUNCALLABLE instance invocation OK~%")
        (format t "FUNCALLABLE instance invocation FAIL: ~A~%" res)))
  (let* ((slot (car (class-slots (class-of inst))))
         (loc (slot-value slot 'location)))
    (setf (funcallable-standard-instance-access inst loc) 42)
    (if (= (slot-value inst 'val) 42)
        (format t "FUNCALLABLE-STANDARD-INSTANCE-ACCESS OK~%")
        (format t "FUNCALLABLE-STANDARD-INSTANCE-ACCESS FAIL: ~A~%"
                (slot-value inst 'val)))))

(defgeneric fgf (x))
(defmethod fgf ((x integer)) :ok)
(set-funcallable-instance-function
 (symbol-function 'fgf)
 (function (lambda (x) :custom)))

(let ((res (fgf 1)))
  (if (eq res :custom)
      (format t "SET-FUNCALLABLE-INSTANCE-FUNCTION on GF OK~%")
      (format t "SET-FUNCALLABLE-INSTANCE-FUNCTION on GF FAIL: ~A~%" res)))
