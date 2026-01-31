(format t "Testing operator method combination (+)...~%")

(defclass op-base () ())
(defclass op-sub (op-base) ())

(defgeneric sum (a b) (:method-combination +))
(defmethod sum + ((a op-base) (b op-base)) 1)
(defmethod sum + ((a op-sub) (b op-base)) 2)

(let ((res (sum (make-instance 'op-sub) (make-instance 'op-base))))
  (if (= res 3)
      (format t "Operator + PASS~%")
      (format t "Operator + FAIL: ~A~%" res)))

(format t "Testing short-form define-method-combination...~%")

(define-method-combination sumcomb :operator + :identity-with-one-argument t)
(defgeneric sum2 (a) (:method-combination sumcomb))
(defmethod sum2 sumcomb ((a op-base)) 10)
(defmethod sum2 sumcomb ((a op-sub)) 20)

(let ((res (sum2 (make-instance 'op-sub))))
  (if (= res 30)
      (format t "Short-form combination PASS~%")
      (format t "Short-form combination FAIL: ~A~%" res)))

(format t "Testing long-form method combination (call-method/make-method)...~%")

(define-method-combination sum+1 ()
  (primaries () :required t)
  (let ((primary (car primaries))
        (next (cdr primaries)))
    `(+ 1
        (call-method ,primary ,next)
        (call-method (make-method 5)))))

(defgeneric score (a) (:method-combination sum+1))
(defmethod score ((a op-base)) 10)
(defmethod score ((a op-sub)) (+ 20 (call-next-method)))

(let ((res (score (make-instance 'op-sub))))
  (if (= res 36)
      (format t "Long-form combination PASS~%")
      (format t "Long-form combination FAIL: ~A~%" res)))
