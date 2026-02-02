(format t "Starting Metaobject Class Test...~%")

(defun member (item list)
  (if (null list)
      nil
      (if (eq item (car list))
          list
          (member item (cdr list)))))

(defclass person ()
  ((name :initarg :name)
   (age :initarg :age)))

(defclass employee (person)
  ((title :initarg :title)))

(let* ((pc (find-class 'person))
       (sc (find-class 'standard-class)))
  (if (eq (class-of pc) sc)
      (format t "CLASS-OF on class object OK~%")
      (format t "CLASS-OF on class object FAIL~%"))

  (if (eq (slot-value pc 'name) 'person)
      (format t "CLASS name slot OK~%")
      (format t "CLASS name slot FAIL~%"))

  (let ((supers (slot-value pc 'direct-superclasses)))
    (if (and supers (eq (car supers) (find-class 'standard-object)))
        (format t "DIRECT-SUPERCLASSES slot OK~%")
        (format t "DIRECT-SUPERCLASSES slot FAIL~%")))

  (let ((subs (slot-value pc 'direct-subclasses)))
    (if (member (find-class 'employee) subs)
        (format t "DIRECT-SUBCLASSES slot OK~%")
        (format t "DIRECT-SUBCLASSES slot FAIL~%")))

  (let ((dslots (slot-value pc 'direct-slots)))
    (if (and dslots (eq (slot-definition-name (car dslots)) 'name))
        (format t "DIRECT-SLOTS slot OK~%")
        (format t "DIRECT-SLOTS slot FAIL~%")))

  (let ((cpl (slot-value pc 'class-precedence-list)))
    (if (and cpl (eq (car cpl) pc))
        (format t "CLASS-PRECEDENCE-LIST slot OK~%")
        (format t "CLASS-PRECEDENCE-LIST slot FAIL~%")))

  (let ((slots (slot-value pc 'slots)))
    (if (and slots (eq (slot-definition-name (car slots)) 'name))
        (format t "SLOTS slot OK~%")
        (format t "SLOTS slot FAIL~%")))

  (let ((finalized (slot-value pc 'finalized-p)))
    (if finalized
        (format t "FINALIZED-P slot OK~%")
        (format t "FINALIZED-P slot FAIL~%")))

  (let ((sz (slot-value pc 'instance-size)))
    (if (= sz 2)
        (format t "INSTANCE-SIZE slot OK~%")
        (format t "INSTANCE-SIZE slot FAIL~%"))))
