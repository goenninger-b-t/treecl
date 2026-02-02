(print "TAGBODY TEST")
(let ((x 0))
  (tagbody
    (setq x 1)
    (go end)
    (setq x 999)
   end
    (print x))
  (print "DONE A")
  
  (let ((i 0))
    (tagbody
      start
      (if (= i 10) (go end) nil)
      (print i)
      (setq i (+ i 1))
      (go start)
      end)
    (print i)
  )
)
