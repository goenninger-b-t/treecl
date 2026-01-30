(defun sum-down (n acc)
  (if (= n 0)
      acc
      (sum-down (- n 1) (+ acc n))))

(print "Starting TCO test...")
(print (sum-down 1000000 0))
(print "Finished TCO test.")
