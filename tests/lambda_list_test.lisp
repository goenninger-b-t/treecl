(print "Testing Lambda Lists...")

;; 1. Required
(print "Test Required:")
(defun test-req (a b) (list a b))
(print (test-req 1 2)) 
;; Errors (manual verify): (test-req 1), (test-req 1 2 3)

;; 2. Optional
(print "Test Optional:")
(defun test-opt (a &optional b (c 10)) (list a b c))
(print (test-opt 1))      ;; Expect: (1 nil 10)
(print (test-opt 1 2))    ;; Expect: (1 2 10)
(print (test-opt 1 2 3))  ;; Expect: (1 2 3)

;; 3. Optional with supplied-p
(print "Test Optional Supplied-p:")
(defun test-opt-sup (a &optional (b 2 b-sup)) (list a b b-sup))
(print (test-opt-sup 1))   ;; Expect: (1 2 nil)
(print (test-opt-sup 1 3)) ;; Expect: (1 3 t)

;; 4. Rest
(print "Test Rest:")
(defun test-rest (a &rest r) (list a r))
(print (test-rest 1))      ;; Expect: (1 nil)
(print (test-rest 1 2 3))  ;; Expect: (1 (2 3))

;; 5. Key
(print "Test Key:")
(defun test-key (a &key b (c 10) (d 20 d-sup)) (list a b c d d-sup))
(print (test-key 1 :b 2))              ;; Expect: (1 2 10 20 nil)
(print (test-key 1 :b 2 :c 30 :d 40))  ;; Expect: (1 2 30 40 t)
(print (test-key 1 :d 50 :c 60))       ;; Expect: (1 nil 60 50 t)

;; 6. Aux
(print "Test Aux:")
(defun test-aux (a &aux (b (list a a))) (list a b))
(print (test-aux 10)) ;; Expect: (10 (10 10))

;; 7. Allow Other Keys
(print "Test Allow Other Keys:")
(defun test-aok (&key a &allow-other-keys) (list a))
(print (test-aok :a 1 :b 2)) ;; Expect: (1)

(print "Done.")
