(format t "Starting Metaobject GF/Method/SlotDefinition Test...~%")

(defclass person ()
  ((name :initarg :name)))

(defgeneric greet (obj))

(defmethod greet ((obj person))
  (slot-value obj 'name))

(let* ((gf (symbol-function 'greet))
       (sgf (find-class 'standard-generic-function))
       (sm (find-class 'standard-method)))
  (if (eq (class-of gf) sgf)
      (format t "GENERIC-FUNCTION class-of OK~%")
      (format t "GENERIC-FUNCTION class-of FAIL~%"))

  (if (eq (slot-value gf 'name) 'greet)
      (format t "GENERIC-FUNCTION name slot OK~%")
      (format t "GENERIC-FUNCTION name slot FAIL~%"))

  (let ((ll (slot-value gf 'lambda-list)))
    (if (and ll (eq (car ll) 'obj) (null (cdr ll)))
        (format t "GENERIC-FUNCTION lambda-list slot OK~%")
        (format t "GENERIC-FUNCTION lambda-list slot FAIL~%")))

  (let* ((methods (slot-value gf 'methods))
         (m (car methods)))
    (if (eq (class-of m) sm)
        (format t "METHOD class-of OK~%")
        (format t "METHOD class-of FAIL~%"))

    (let ((quals (slot-value m 'qualifiers)))
      (if (null quals)
          (format t "METHOD qualifiers slot OK~%")
          (format t "METHOD qualifiers slot FAIL~%")))

    (let ((specs (slot-value m 'specializers)))
      (if (and specs (eq (car specs) (find-class 'person)) (null (cdr specs)))
          (format t "METHOD specializers slot OK~%")
          (format t "METHOD specializers slot FAIL~%")))

    (let ((gf-slot (slot-value m 'generic-function)))
      (if (eq gf-slot gf)
          (format t "METHOD generic-function slot OK~%")
          (format t "METHOD generic-function slot FAIL~%")))

    (let ((fn (slot-value m 'function)))
      (if fn
          (format t "METHOD function slot OK~%")
          (format t "METHOD function slot FAIL~%")))))

(let* ((pc (find-class 'person))
       (dslot (car (class-direct-slots pc)))
       (eslot (car (class-slots pc))))
  (if (eq (class-of dslot) (find-class 'standard-direct-slot-definition))
      (format t "DIRECT-SLOT-DEFINITION class-of OK~%")
      (format t "DIRECT-SLOT-DEFINITION class-of FAIL~%"))

  (if (eq (class-of eslot) (find-class 'standard-effective-slot-definition))
      (format t "EFFECTIVE-SLOT-DEFINITION class-of OK~%")
      (format t "EFFECTIVE-SLOT-DEFINITION class-of FAIL~%"))

  (if (eq (slot-value dslot 'name) 'name)
      (format t "SLOT-DEFINITION name slot OK~%")
      (format t "SLOT-DEFINITION name slot FAIL~%"))

  (let ((initargs (slot-value dslot 'initargs)))
    (if (and initargs (eq (car initargs) :name))
        (format t "SLOT-DEFINITION initargs slot OK~%")
        (format t "SLOT-DEFINITION initargs slot FAIL~%")))

  (if (eq (slot-value dslot 'allocation) :instance)
      (format t "SLOT-DEFINITION allocation slot OK~%")
      (format t "SLOT-DEFINITION allocation slot FAIL~%")))
