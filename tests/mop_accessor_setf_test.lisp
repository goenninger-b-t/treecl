(format t "Starting MOP Accessor SETF Test...~%")

(defclass accessor-setf-test ()
  ((x :accessor foo)))

(defparameter *before-hit* nil)

(defmethod (setf foo) :before (value (obj accessor-setf-test))
  (declare (ignore value obj))
  (setf *before-hit* t))

(let ((obj (make-instance 'accessor-setf-test)))
  (setf *before-hit* nil)
  (setf (foo obj) 10)
  (if *before-hit*
      (format t "SETF accessor :before OK~%")
      (format t "SETF accessor :before FAIL~%"))
  (if (= (foo obj) 10)
      (format t "SETF accessor basic OK~%")
      (format t "SETF accessor basic FAIL~%"))

  (setf *before-hit* nil)
  (setf (foo obj) 99)
  (if *before-hit*
      (format t "SETF accessor :before repeat OK~%")
      (format t "SETF accessor :before repeat FAIL~%"))
  (if (= (foo obj) 99)
      (format t "SETF accessor update OK~%")
      (format t "SETF accessor update FAIL~%"))

  (if (fboundp 'foo)
      (format t "FBOUNDP reader OK~%")
      (format t "FBOUNDP reader FAIL~%"))

  (if (fboundp '(setf foo))
      (format t "FBOUNDP (setf foo) OK~%")
      (format t "FBOUNDP (setf foo) FAIL~%"))

  (let ((gf (symbol-function '(setf foo))))
    (if (equal (generic-function-name gf) '(setf foo))
        (format t "GENERIC-FUNCTION-NAME setf OK~%")
        (format t "GENERIC-FUNCTION-NAME setf FAIL~%"))
    (let ((gf2 (ensure-generic-function '(setf foo))))
      (if (eq gf gf2)
          (format t "ENSURE-GENERIC-FUNCTION setf OK~%")
          (format t "ENSURE-GENERIC-FUNCTION setf FAIL~%"))))

  (let ((gf3 (symbol-function 'foo)))
    (if (eq (generic-function-name gf3) 'foo)
        (format t "GENERIC-FUNCTION-NAME reader OK~%")
        (format t "GENERIC-FUNCTION-NAME reader FAIL~%"))))
