(format t "Testing Loop Scope...~%")

(let ((x 1))
  (loop
     (if (> x 5) (return x))
     (format t "x=~A~%" x)
     (incf x)))

(format t "Loop finished.~%")
