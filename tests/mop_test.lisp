
(format t "Starting MOP Test...~%")

(defclass person ()
  ((name :initarg :name :accessor person-name)
   (age :initarg :age :initform 0 :accessor person-age)))

(defparameter p1 (make-instance 'person :name "Alice" :age 30))
(format t "P1 Name: ~A, Age: ~A~%" (slot-value p1 'name) (slot-value p1 'age))

(if (and (string-equal (slot-value p1 'name) "Alice")
         (= (slot-value p1 'age) 30))
    (format t "Initargs TEST PASS~%")
    (format t "Initargs TEST FAIL~%"))

(defclass employee (person)
  ((title :initarg :title :accessor employee-title)))

(defparameter e1 (make-instance 'employee :name "Bob" :age 40 :title "Engineer"))
(format t "E1 Name: ~A, Title: ~A~%" (slot-value e1 'name) (slot-value e1 'title))

(if (and (string-equal (slot-value e1 'name) "Bob")
         (string-equal (slot-value e1 'title) "Engineer"))
    (format t "Inheritance Initargs TEST PASS~%")
    (format t "Inheritance Initargs TEST FAIL~%"))

;; Test Method Dispatch
(defgeneric greet (obj))

(defmethod greet ((p person))
  (format nil "Hello, ~A" (slot-value p 'name)))

(defmethod greet ((e employee))
  (format nil "Employee ~A says: ~A" (slot-value e 'title) (call-next-method)))

(format t "Greeting P1: ~A~%" (greet p1))
(format t "Greeting E1: ~A~%" (greet e1))
