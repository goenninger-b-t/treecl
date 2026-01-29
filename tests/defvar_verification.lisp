(defvar *a* nil)
(format t "VAR A: ~A~%" *a*)
(if (boundp '*a*) (format t "BOUND YES~%") (format t "BOUND NO~%"))
(symbol-name *a*)
