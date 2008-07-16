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
    

(defun rr-expander (form)
  "Returns two values, the first is T if a match was achieved,
the second is then the expansion.
   If no match was possible, the first value is NIL and the 
second is the original form"
  (multiple-value-bind (match-1 expansion-1)
      (let ((car-var (car form))
	    (cdr-var (cdr form)))
	(if (eql car-var 'rr-example)
	    (if (null cdr-var)
		(values t '(8 rl))
		(values nil form))
	    (values nil form)))
    (if match-1 (values match-1 expansion-1)
	(multiple-value-bind (match-2 expansion-2)
	    (let ((car-var (car form))
		  (cdr-var (cdr form)))
	      (if (eql car-var 'rr-example)
		  (let ((?place (car cdr-var))
			(cddr-var (cdr cdr-var)))
		    (if (null cddr-var)
			(values t `(seq push (l ,@?place) 
					rr-example (st ,@?place) 
					pop))
			(values nil form)))
		  (values nil form)))
	  (if match-2 
	      (values match-2 expansion-2)
	      (values nil form))))))

(rr-expander '(rr-example)) 

;; --> T, (8 RL)

(rr-expander '(rr-example (loc)))

;; --> T, (SEQ PUSH (L LOC) RR-EXAMPLE (ST LOC) POP)

(rr-expander '(rr-mismatch))

;; --> NIL, (RR-MISMATCH)
                   	  
