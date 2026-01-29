(format t "Testing simple progn~%")
(progn (format t "Progn works~%"))

(format t "Testing let with progn~%")
(let ((x 1)) (progn x))

(format t "Testing empty progn~%")
(progn)

;; (format t "Testing progn as variable (should fail)~%")
;; progn

(format t "Done~%")
