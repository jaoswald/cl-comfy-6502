;;; macro-test.lisp

(defun match-variable-p (thing)
  (and (symbolp thing) (char= (char (symbol-name thing) 0) #\?)))

(defun match-predicate (x)
  (and (consp x) (eq (car x) :in)))

(defun bindings-created (pattern &optional existing)
  (cond
    ((null pattern) nil)
    ((match-variable-p pattern) 
     (if (member pattern existing)
	 nil
	 (list pattern)))
    ((atom pattern) nil)
    ((eq (car pattern) 'quote) nil)
    ((match-predicate pattern)
     (if (endp (cddr pattern))
	 (let ((var (caddr pattern)))
	   (if (member var existing)
	       nil 
	       (list var)))))
    (t ; pattern is a CONS
     (let ((car-bindings (bindings-created (car pattern)
					   existing)))
       (append car-bindings (bindings-created (cdr pattern)
					      (append car-bindings
						      existing)))))))
    
  