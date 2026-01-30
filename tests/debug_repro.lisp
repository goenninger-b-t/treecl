(format t "Test 1: Simple symbol~%")
(let ((s 'progn))
  (format t "S: ~A~%" s))

(format t "Test 2: Car of list~%")
(let ((x (list 'progn)))
  (let ((y (car x)))
    (format t "Y: ~A~%" y)))

(format t "Test 3: Macro definition~%")
(defmacro m () '(progn))

(format t "Test 4: Macroexpand~%")
(let ((exp (macroexpand-1 '(m))))
  (format t "Exp: ~A~%" exp)
  (let ((form (car exp)))
    (format t "Form: ~A~%" form)
    (let ((sym (car form)))
       (format t "Sym: ~A~%" sym))))
