;; Test SETF functionality
(format t "Starting SETF Tests~%")

(defvar *failures* 0)

(defmacro check (form expected &optional note)
  `(let ((val ,form)
         (exp ,expected))
     (if (equal val exp)
         (format t "PASS: ~a -> ~a~%" ',form val)
         (progn
           (format t "FAIL: ~a~%  Expected: ~a~%  Got:      ~a~%  Note: ~a~%" ',form exp val ,note)
           (incf *failures*)))))

;; 1. Simple SETF Variable
(format t "--- Variable SETF ---~%")
(defparameter *x* 10)
(check *x* 10 "Initial Value")
(setf *x* 20)
(check *x* 20 "After SETF")

;; 2. CAR/CDR
(format t "--- CAR/CDR SETF ---~%")
(defparameter *l* (list 1 2 3))
(check (car *l*) 1)
(setf (car *l*) 100)
(check (car *l*) 100 "Setf CAR")
(check *l* '(100 2 3))

(setf (cdr *l*) '(4 5))
(check *l* '(100 4 5) "Setf CDR")
(setf (cadr *l*) 200) ;; Requires setf expander for cadr? No, cadr is macro (car (cdr ...))?
;; If cadr is function, we need expander.
;; if cadr is macro (car (cdr x)), setf should expand place.
(check (cadr *l*) 4)
;; (setf (cadr *l*) 200) ;; Uncomment if cadr is macro or handled
;; TreeCL init.lisp defines (defun cadr (x) (car (cdr x))) ??
;; If cadr is function, we need defsetf.
;; If cadr is not defined, we might fail.
;; Let's check (second *l*) if available.

;; 3. PLISTS
(format t "--- PLIST SETF ---~%")
(defparameter *sym* 'my-symbol)
(setf (get *sym* 'color) 'red)
(check (get *sym* 'color) 'red "Setf GET")
(setf (get *sym* 'color) 'blue)
(check (get *sym* 'color) 'blue "Update GET")

;; 4. AREF
(format t "--- AREF SETF ---~%")
(defparameter *vec* (make-array 3))
(setf (aref *vec* 0) 10)
(setf (aref *vec* 1) 20)
(check (aref *vec* 0) 10)
(check (aref *vec* 1) 20)

;; 5. DEFSETF Short
(format t "--- DEFSETF Short ---~%")
(defvar *storage* (make-array 5))
(defun my-access (idx) (aref *storage* idx))
(defun my-update (idx val) (setf (aref *storage* idx) val))
(defsetf my-access my-update)

(setf (my-access 2) 99)
(check (my-access 2) 99 "Short DEFSETF")
(check (aref *storage* 2) 99)

;; 6. DEFSETF Long
(format t "--- DEFSETF Long ---~%")
(defvar *cell* (cons nil nil))
(defun cell-val () (car *cell*))
(defsetf cell-val () (store)
  `(setf (car *cell*) ,store))

(setf (cell-val) 77)
(check (cell-val) 77 "Long DEFSETF")

(format t "Failures: ~a~%" *failures*)
