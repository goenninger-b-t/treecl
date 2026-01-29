(print "BLOCK TEST")

;; 1. Implicit Progn
(print 
  (block simple
    (print "Inside simple")
    10))
;; Expect: Inside simple, 10

;; 2. Return-From
(print
  (block early
    (print "Start early")
    (return-from early 20)
    (print "Should not print")
    30))
;; Expect: Start early, 20

;; 3. Nested Shadowing
(print
  (block outer
    (block outer ;; Shadowing
      (return-from outer 40))
    50))
;; Expect: 50 (Inner block returned 40 to Outer's body, which continued to 50)
;; Wait. (block outer (return-from outer 40)) evaluates to 40.
;; Then outer block continues?
;; Yes, because inner 'outer' block caught the return.
;; So result of inner block is 40.
;; Then outer block has form 50.
;; So result is 50. Correct.

;; 4. Return from Outer
(print
  (block outer
    (block inner
      (return-from outer 60)
      (print "Should not print inner"))
    (print "Should not print outer")))
;; Expect: 60

(print "DONE BLOCK")
