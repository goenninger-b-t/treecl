(cl:in-package :cl-user)

(defun frgo (x)
    (format t "~&*** ~A ***~&" x)
    (error "Hi! 12345"))

(defun frgo1 (x)
    (format t "~&*** ~A ***~&" x)
    (frgo x))

(defun frgo2 ()
    (let x ((frgo 1)
    (frgo1 x))))

