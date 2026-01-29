;; Test simple macro
(format t "Testing macro expansion...~%")

(defmacro test-macro ()
  '(progn
     (format t "Macro Progn Works~%")
     t))

(format t "Checking PROGN package...~%")
(let ((p (symbol-package 'progn)))
  (format t "Package of 'progn: ~A~%" p))

(format t "Checking expansion symbol...~%")
(let ((exp (macroexpand-1 '(test-macro))))
  (let ((form (car exp)))
     (let ((sym (car form)))
        (format t "Symbol in expansion: ~A~%" sym)
        (format t "Package of expansion symbol: ~A~%" (symbol-package sym))
        (if (eq sym 'progn)
            (format t "EQ to 'progn: YES~%")
            (format t "EQ to 'progn: NO~%")))))

(format t "Checking execution...~%")
(if (test-macro)
    (format t "Success~%")
    (format t "Failure~%"))

(defmacro test-backquote ()
  `(progn (format t "Backquote Progn Works~%")))

(test-backquote)

(format t "Done~%")
