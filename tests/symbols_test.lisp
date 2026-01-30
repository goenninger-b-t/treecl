(print "Starting Symbols Test")

;; SYMBOL-NAME
(assert (equal (symbol-name 'foo) "FOO"))
(assert (equal (symbol-name :foo) "FOO"))
(assert (equal (symbol-name 'cl-user::bar) "BAR"))

;; SYMBOL-PACKAGE
(assert (equal (package-name (symbol-package 'foo)) "CL-USER"))
(assert (equal (package-name (symbol-package :foo)) "KEYWORD"))
(assert (equal (symbol-package (make-symbol "GENSYM")) nil))

;; VALUE BINDING
(set 'my-var 42)
(assert (boundp 'my-var))
(assert (equal (symbol-value 'my-var) 42))
(makunbound 'my-var)
(assert (not (boundp 'my-var)))

;; PLIST
(setf (get 'my-sym 'prop1) "val1")
(assert (equal (get 'my-sym 'prop1) "val1"))
(assert (equal (get 'my-sym 'prop2) nil))
(assert (equal (get 'my-sym 'prop2 "default") "default"))

(remprop 'my-sym 'prop1)
(assert (equal (get 'my-sym 'prop1) nil))
(assert (null (symbol-plist 'my-sym)))

;; FUNCTION BINDING
;; Note: We can't easily defun in test without valid lambda, but we can check standard funcs
(assert (fboundp 'car))
(assert (not (fboundp 'undefined-func-123)))
;; (symbol-function 'car) returns opaque, but should not error

;; PACKAGES
(assert (find-package "COMMON-LISP"))
(assert (find-package "CL"))
(assert (find-package :cl))
(assert (equal (package-name (find-package "CL")) "COMMON-LISP"))

(assert (listp (list-all-packages)))

;; TYPES
(assert (keywordp :foo))
(assert (not (keywordp 'foo)))

;; COPY-SYMBOL
(set 'orig 100)
(let ((copy (copy-symbol 'orig)))
  (assert (equal (symbol-name copy) "ORIG"))
  (assert (null (symbol-package copy)))
  (assert (not (boundp copy)))) ;; Default copy doesn't copy props

(print "Symbols Test Passed")
