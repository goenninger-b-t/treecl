;; Minimal reproduction
(print "Testing DOLIST...")
(dolist (x '(1 2 3))
  (print x))

(print "Testing LOOP...")
(let ((i 0))
  (loop
    (print i)
    (setq i (+ i 1))
    (if (> i 3) (return))))

(print "Testing DEFMETHOD macro logic manually...")
(let ((rest '(magnitude ((p point)))))
  (print "Rest before:")
  (print rest)
  (loop
    (if (and (consp rest) (symbolp (car rest)))
        (print "Qualifier found")
        (return)))
  (print "Loop finished"))

(print "Testing Actual DEFMETHOD...")
(defmethod test-method ((x t))
  (print x))
(print "Defined.")
(test-method 10)
