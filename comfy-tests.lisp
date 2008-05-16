;;;; -*- mode: Lisp; Syntax: ANSI-Common-Lisp; Package: (COMFY-6502-TESTS ("COMFY-6502" "RT")); -*-
;;;;
;;;; comfy-tests.lisp
;;;;
;;;; Uses RT regression test framework

(cl:defpackage "COMFY-6502-TESTS"
  (:use "COMMON-LISP" "6502" "COMFY-6502" #+sbcl "SB-RT" #-sbcl "RT")
  (:shadowing-import-from "COMFY-6502" 
			  "COMPILE" "1+" "1-" "+" "-" "IF" "NOT" "LOOP"
			  "FOR"
			  "BREAK"))

(in-package "COMFY-6502-TESTS")

;;; test emission of code

(defun simple-gen ()
  (init)
  (comfy-6502::gen 1)
  (comfy-6502::gen 2)
  comfy-6502::*mem*)

(deftest simple-gen-1 (init) 0)
(deftest simple-gen-2 (progn (init) (comfy-6502::gen 1)) 1)
(deftest simple-gen-3 (simple-gen) (2 1))

(defgeneric to-opcode (thing)
  (:method ((thing t))
    thing)
  (:method ((thing 6502:symbolic-opcode))
    (cons (opcode thing) 
	       (cl:if (member (address-mode thing) 
			      '(:IMPLIED :ACCUMULATOR :BRANCH-RELATIVE))
		      nil
		      (list (address-mode thing))))))

(defmacro code-result (&body forms)
  `(progn
    (init)
    ,@forms
    (map 'list #'to-opcode comfy-6502:*mem*)))

(defmacro compile-code (comfy-form &optional (win 0) (lose 0))
  `(code-result (comfy-6502:compile ',comfy-form ,win ,lose)))

(defmacro code-result-and-value (&body comfy-forms)
  (let ((result (gensym)))
    `(let (,result)
      (values 
       (code-result (setq ,result (progn ,@comfy-forms)))
       ,result))))


(deftest branch-1 (code-result (comfy-6502::genbr 0))
  ((JMP :ABSOLUTE) (:LONG-BRANCH 2)))
   ; 3                   2        1

(deftest branch-1b (progn
		     (init)
		     (comfy-6502::genbr 0)
		     (map 'list #'to-opcode
			  (relocate comfy-6502::*mem* 97)))
  ((JMP :ABSOLUTE) 100 0))
   ; 97            ; 98 99 

(deftest branch-2 
    ;; conditional jump: win and lose destinations both longer than
    ;; 8-bit branch [case 8, then 7, then 4]
    (code-result (comfy-6502::genbrc '6502:BCC 
				     -1000
				     -2000))

  ;; inverts condition to skip three-byte long jump to win, landing on 
  ;; long jump to lose 
  
  ((BCS) (:BRANCH 4) 
   (JMP :ABSOLUTE) (:LONG-BRANCH 1005) 
   (JMP :ABSOLUTE) (:LONG-BRANCH 2002)))

(deftest branch-3
    ;; conditional jump: win and lose destinations both within 8-bit
    ;; branch [case 5]
    (code-result (comfy-6502::genbrc '6502:BEQ -10 90))
  ;; branch to win, branch with opposite condition to lose
  ((BEQ) (:BRANCH 13) (BNE) (:BRANCH -89)))

(deftest branch-4
    ;; conditional jump: win is current location, lose within 8-bit branch
    (code-result (comfy-6502::genbrc 'BVC 0 90))
  ;; invert condition to branch to lose, fall through to win
  ((BVS) (:BRANCH -89)))

(deftest branch-5
    ;; conditional jump: win is within 8-bit branch, lose is current location
    (code-result (comfy-6502::genbrc 'BPL -10 0))
    ;; short branch with win condition, fall through to lose
  ((BPL) (:BRANCH 11)))

(deftest branch-6
    ;; both win and lose are the same and fall through: don't need test
    (code-result-and-value (comfy-6502::genbrc 'BMI 0 0))
  nil 0)

(deftest branch-7
    ;; both win and lose are the same, destination *not* fall through
    (code-result-and-value (comfy-6502::genbrc 'BMI -100 -100))
  nil -100)

(deftest branch-8
    ;; both win and lose are short branches, but only if "win branch"
    ;; is emitted first [case 6]
    (code-result (comfy-6502::genbrc 'BNE -127 -100))
  ((BEQ) (:BRANCH 103) (BNE) (:BRANCH 128)))

#||
(deftest "branch"
    (assert-equal 100 (init))
  (assert-equal 97 (genbr (+ (* 256 111) 222)))
  (assert-equal 97 *f*)
  ;; unconditional jump, two byte address, LSB first
  (assert-equal '[JMP 222 111] (subseq *mem* f))
  ;; conditional jump: win and lose destinations both longer than
  ;; 8-bit branch [case 8, then 7, then 4]
  (assert-equal 89 (genbrc 'BCC (+ (* 256 102) 101) (+ (* 256 202) 201)))
  (assert-equal 89 f)
  ;; inverts condition to skip three-byte long jump to win, landing on 
  ;; long jump to lose [case 5]
  (assert-equal '[BCS 3 JMP 101 102 JMP 201 202] (subvector *mem* f (+ f 8)))

  ;; conditional jump: win and lose destinations both within 8-bit
  ;; branch [case 5]
  (assert-equal 85 (genbrc 'BEQ 97 10))
  (assert-equal 85 f)
  ;; branch to win, branch with opposite condition to lose
  ;; FIXED BUG: I think the BEQ destination is wrong: 87 + 6 = 93, not 97
  ;;; WAS BEQ 6 BNE -79
  ;;; JAO: fixed
  (assert-equal '[BEQ 10 BNE -79]
(subvector *mem* f (+ f 4)))

  ;; conditional jump: win is current location, lose within 8-bit branch
  (assert-equal 83 (genbrc 'BVC 85 10))
  (assert-equal 83 f)
  ;; invert condition to branch to lose, fall through to win
  (assert-equal '[BVS -75] 
(subvector *mem* f (+ f 2)))
  
  ;; conditional jump: win is within 8-bit branch, lose is current location
  (assert-equal 81 (genbrc 'BPL 101 83))
  ;; short branch with win condition, fall through to lose
  ;; 83 + 18 = 101
  (assert-equal '[BPL 18] 
(subvector *mem* f (+ f 2)))
  
  ;; both win and lose are the same and fall through: don't need test
  ;; but what should the return value be? gen routines seem to 
  ;; return f; is that conceptually identical to "win" in all cases?
  (assert-equal 81 (genbrc 'BMI 81 81))
  (assert-equal 81 f)

  ;; both win and lose are the same, destination *not* fall through
  ;; this should be an unconditional branch to win?
  ;; NOT necessarily: return value is continuation
  (assert-equal 100 (genbrc 'BMI 100 100))
  (assert-equal 81 f)

  ;; both win and lose are short branches, but only if "win branch"
  ;; is emitted first [case 6]
  (assert-equal 77 (genbrc 'BNE (+ f 127) (+ f 100)))
  (assert-equal 77 f)
  (assert-equal '[BEQ 102 BNE 127] (subvector *mem* f (+ f 4))))
||#

(deftest compile-cmp-1 (compile-code (seq (l \# 10) (c j 20)))
  ((LDA :IMMEDIATE) (:BYTE 10)
   (CMP :ABSOLUTE-Y) 
   (:ABSOLUTE 20)))

(deftest compile-cmp-1b (compile-code (seq (l \# 10)))
  ((LDA :IMMEDIATE) (:BYTE 10)))

(deftest compile-cmp-1c (compile-code (seq (c j 20)))
  ((CMP :ABSOLUTE-Y) (:ABSOLUTE 20)))

(deftest compile-1b (compile-code (seq))
  ())

(deftest compile-1 (compile-code (seq c=0 v=0 binary decimal enable disable)) 
  ((CLC) (CLV) (CLD) (SED) (CLI) (SEI)))

(deftest compile-2 (compile-code (not (loop (li s) ~=0? pop)))
  ;; clear the stack
  ((TSX) (BEQ) (:BRANCH 5) (PLA) (JMP :ABSOLUTE) (:LONG-BRANCH -5)))

(deftest compile-3 (progn
		     (defparameter *n* 32)  ; address of counter
		     (defparameter *len* 2) ; number of bytes
		     (compile-code (seq (li \# 0)
					c=1     ; initial (+ \# 0) will add 1
					(while c=1?
					  (seq (ci \# (lisp *len*))
					       LLT ; wins if X < #*len* unsign
					       (l i (lisp *n*))
					       (+ \# 0) 
					       (st i (lisp *n*)) 
					       i+1))) 
				   0 -10))
  ((LDX :IMMEDIATE) (:BYTE 0)    ;; [19] 
   (SEC)                 ;; [17]
   (BCC) (:BRANCH 15)    ;; [16] if done incrementing, WIN -> 0
   (CPX :IMMEDIATE) (:BYTE 2)    ;; [14]
   (BCS) (:BRANCH 21)    ;; [12] X>=#*len* means *n* overflowed: LOSE -> 110
   (LDA :ZERO-PAGE-X) (:ZERO-PAGE 32) ;; [10]
   (ADC :IMMEDIATE) (:BYTE 0)    ;; [8]
   (STA :ZERO-PAGE-X) (:ZERO-PAGE 32) ;; [6]
   (INX)                 ;; [4]
   (JMP :ABSOLUTE) (:LONG-BRANCH -14))) ;; [3]

;; same tests as compile-3, but put in a neat extra inversion of the
;; CPX test...comfy takes it!

(deftest compile-3b (progn
		      (defparameter *n* 32)
		      (defparameter *len* 2) ; number of bytes
		      (compile-code (seq (li \# 0)
					 c=1    ; initial (+ \# 0) will add 1
					 (while c=1?
					   (seq (ci \# (lisp *len*))
						(not LGE) ; lose if X >= #*len*
						(l i (lisp *n*))
						(+ \# 0) 
						(st i (lisp *n*))
						i+1))) 
				    0 -10))
  ((LDX :IMMEDIATE) (:BYTE 0)    ;; [19] 
   (SEC)                 ;; [17]
   (BCC) (:BRANCH 15)    ;; [16] if done incrementing, WIN -> 0
   (CPX :IMMEDIATE) (:BYTE 2)    ;; [14]
   (BCS) (:BRANCH 21)    ;; [12] *len*-byte quantity overflowed: LOSE -> -10
   (LDA :ZERO-PAGE-X) (:ZERO-PAGE 32) ;; [10]
   (ADC :IMMEDIATE) (:BYTE 0)    ;; [8]
   (STA :ZERO-PAGE-X) (:ZERO-PAGE 32) ;; [6]
   (INX)                 ;; [4]
   (JMP :ABSOLUTE)       ;; [3]
   (:LONG-BRANCH -14)))  ;; [2] --> BCC

(deftest alt-1 (comfy-macroexpand '(alt (seq <0? (1+ *m*))
					(seq (1- *b*) =0?)))
  (not (seq (not (seq <0? (1+ *m*)))
	    (not (seq (1- *b*) =0?)))))

(deftest compile-4 (progn
		     (defparameter *m* 10)
		     (defparameter *b* 11)
		     (compile-code (alt (seq <0? (1+ (lisp *m*)))
					(seq (1- (lisp *b*)) =0?))
				   -10 -20))
  ((BPL) (:BRANCH 6)                 ; [13] [first ALT clause loses, try second
   (INC :ZERO-PAGE) (:ZERO-PAGE 10)  ; [11] first ALT clause wins, try second
   (JMP :ABSOLUTE)  (:LONG-BRANCH 18) ; [9] WIN->-10 (first alt won...)
   ;; second clause of alt
   (DEC :ZERO-PAGE)  (:ZERO-PAGE 11) ; [6] (1- *b*) 
   (BEQ)             (:BRANCH 13)    ; [4] WIN->0:  second clause won
   (BNE)             (:BRANCH 21)))  ; [2] LOSE->-20: all alt clauses lost 

(deftest fori-1 (progn 
		  (defparameter *code* 11)
		  (compile-code (fori (\# 6) (\# 12) 
				      (l i (lisp *code*))
				      (lxor \# 127)
				      (st i (lisp *code*))) -10 -20))
  ((LDX :IMMEDIATE) (:BYTE 6)     ; [16]
   (CPX :IMMEDIATE) (:BYTE 12)     ; [14] 
   (BCS) (:BRANCH 21)        ; [12] BCS -10 --> win
   (LDA :ZERO-PAGE-X) (:ZERO-PAGE 11) ; [10] (l i *code*)
   (EOR :IMMEDIATE)  (:BYTE 127)     ; [8] (lxor \# 127)
   (STA :ZERO-PAGE-X) (:ZERO-PAGE 11) ; [6] (st i *code*)
   (INX)                     ; [4]
   (JMP :ABSOLUTE) (:LONG-BRANCH -12))) ; [3]

(deftest forj-1 (progn 
		  (defparameter *code* 11)
		  (compile-code (forj (\# 6) (\# 12) 
				      (l j (lisp *code*))
				      (lxor \# 127)
				      (st j (lisp *code*))) -10 -20))
  ((LDY :IMMEDIATE) (:BYTE 6)           ; [18]
   (CPY :IMMEDIATE) (:BYTE 12)          ; [16] 
   (BCS) (:BRANCH 23)                   ; [14] BCS -10 --> win
   (LDA :ABSOLUTE-Y) (:ABSOLUTE 11)     ; [12] (l j *code*)
   (EOR :IMMEDIATE)  (:BYTE 127)        ; [9]  (lxor \# 127)
   (STA :ABSOLUTE-Y) (:ABSOLUTE 11)     ; [7]  (st j *code*)
   (INY)                                ; [4]
   (JMP :ABSOLUTE) (:LONG-BRANCH -14))) ; [3]  -> to CPY

(deftest for-1 (code-result
		 (equ code 13)  ; buffer 13..25
		 (equ ptr 26)
		 (comfy-6502:compile  
		  '(for (ptr) (\# 6) (\# 12) 
		      (li ptr)
		      (l i code)
		      (lxor \# 127)
		      (st i code)) -10 -20))
  ((LDA :IMMEDIATE) (:BYTE 6)           ; [23]
   (STA :ZERO-PAGE) (:ZERO-PAGE 26)     ; [21]
   (CMP :IMMEDIATE) (:BYTE 12)          ; [19] 
   (BCS) (:BRANCH 26)                   ; [17] BCS -10 --> win
   (LDX :ZERO-PAGE) (:ZERO-PAGE 26)     ; [15]
   (LDA :ZERO-PAGE-X) (:ZERO-PAGE 13)   ; [13] (l j *code*)
   (EOR :IMMEDIATE)  (:BYTE 127)        ; [11] (lxor \# 127)
   (STA :ZERO-PAGE-X) (:ZERO-PAGE 13)   ; [9]  (st j *code*)
   (INC :ZERO-PAGE) (:ZERO-PAGE 26)     ; [7]
   (LDA :ZERO-PAGE) (:ZERO-PAGE 26)     ; [5]
   (JMP :ABSOLUTE) (:LONG-BRANCH -17))) ; [3]   -> to CMP

(deftest upc-example 
    (code-result
;;      (defparameter *upctable* 
;;	(compile '(seq 13 25 19 61 35 49 47 59 55 11) 0 0))
      (equ code 13)  ; buffer 13..25
      (equ mq   12)
      (equ digit 26) ; buffer 26..39
      (comfy-6502:compile  
       '(alt
	 (seq (fori (\# 6) (\# 12) ; complement patterns of right 6 upc digits.
	       (l i code)
	       (lxor \# 127)
	       (st i code))
	  (fori (\# 0) (\# 12)
	   (l i code)
	   (not
	    (forj (\# 0) (\# 10)
		  (c j upc-table)
		  ~=?))             ; fail if equal.
	   (stj i digit))            ; store index of upctable.
	  decimal                         ; set decimal arithmetic mode.
	  (l \# 0)                        ; clear ac.
	  (fori (\# 0) (\# 12)            ; add up the even digits.
	   (+ i digit)               ; loop control clears carry!
	   i+1)                      ; only every other one.
	  (st mq)                         ; save partial sum.
	  c=0                             ; clear the carry.
	  (2 (+ mq))                      ; multiply by 3.
	  (fori (\# 1) (\# 12)            ; add up the odd digits.
	   (+ i digit)               ; loop control clears carry.
	   i+1)                      ; only every other one.
	  (lxor \# 15)                    ; select low decimal digit.
	  =0?                            ; fails if non-zero.
	  return)
	 (seq trap                          ; signal failure.
	  return)) -10 -20))
  ((LDX :IMMEDIATE) (:byte 6)              ;  [2] (fori (\# 6)
   (CPX :IMMEDIATE) (:byte 12)             ;  [4]       (\# 12) ...
   (BCS) (:BRANCH 11)              ;  [6] --> [18] seq2
   (LDA :ZERO-PAGE-X) (:ZERO-PAGE 13) ;  [8]
   (EOR :IMMEDIATE) (:byte 127)            ; [10]
   (STA :ZERO-PAGE-X) (:ZERO-PAGE 13)          ; [12]
   (INX)                           ; [14]
   (JMP :ABSOLUTE) (:LONG-BRANCH -12)  ; [15] -> CPX #12
   (LDX :IMMEDIATE) (:byte 0)              ; [18] seq2: (fori (\# 0) 
   (CPX :IMMEDIATE) (:byte 12)             ; [20]             (\# 12) ...
   (BCS) (:BRANCH 24)              ; [22] --> [47] seq3
   (LDA :ZERO-PAGE-X) (:ZERO-PAGE 13) ; [24]
   (LDY :IMMEDIATE) (:byte 0)              ; [26] (forj (\# 0)
   (CPY :IMMEDIATE) (:byte 10)             ; [28]       (\# 10)
   (BCS) (:BRANCH 57)                        ; [30] --> [88] FAIL
   (CMP :ABSOLUTE-Y) (:ABSOLUTE UPC-TABLE)  ; [32]
   (BEQ) (:BRANCH 5)               ; [35] --> [41] seq3b
   (INY)                           ; [37]
   (JMP :ABSOLUTE) (:LONG-BRANCH -11) ; [38] --> CPY #10
   (STY :ZERO-PAGE-X) (:ZERO-PAGE 26) ; [41]
   (INX)                           ; [43]
   (JMP :ABSOLUTE) (:LONG-BRANCH -25)    ; [44] --> CPX #12
   (SED)                           ; [47] seq3: decimal
   (LDA :IMMEDIATE) (:byte 0)              ; [48]
   (LDX :IMMEDIATE) (:byte 0)              ; [50] (fori (\# 0) 
   (CPX :IMMEDIATE) (:byte 12)             ; [52]       (\# 12) ...
   (BCS) (:BRANCH 8)                         ; [54] --> seq4 [63]
   (ADC :ZERO-PAGE-X) (:ZERO-PAGE 26) ; [56]
   (INX)                           ; [58]
   (INX)                           ; [59]
   (JMP :ABSOLUTE) (:LONG-BRANCH -9) ; [60] --> CPX #12
   (STA :ZERO-PAGE) (:ZERO-PAGE 12)  ; [63] seq4: (st *mq*)
   (CLC)                           ; [65]
   (ADC :ZERO-PAGE) (:ZERO-PAGE 12)            ; [66]
   (ADC :ZERO-PAGE) (:ZERO-PAGE 12)            ; [68]
   (LDX :IMMEDIATE) (:byte 1)              ; [70] (fori (\# 1)
   (CPX :IMMEDIATE) (:byte 12)             ; [72]       (\# 12) ...
   (BCS) (:BRANCH 8)               ; [74] --> seq5: [83]
   (ADC :ZERO-PAGE-X) (:ZERO-PAGE 26) ; [76]
   (INX)                           ; [78]
   (INX)                           ; [79]
   (JMP :ABSOLUTE) (:LONG-BRANCH -9); [80] -> CPX #12
   (EOR :IMMEDIATE) (:byte 15)             ; [83] seq5: (lxor \# 15)
   (BNE) (:BRANCH 2)                         ; [85] -> TRAP at 88
   (RTS)                           ; [87]
   (BRK)                           ; [88]
   (RTS)))                         ; [89]


;;; Test pattern-matching macros similar to Baker's

(deftest match-1 
    (comfy-6502::match '(move ?x ?y) '(move foo bar))
  T ((?x . foo) (?y . bar)))

(deftest match-2 
    (comfy-6502::match '(a b ?c) '(a b foo))
  T ((?c . foo)))

(deftest match-3
    (comfy-6502::match '(a b ?c) '(a b foo bar))
  nil nil)

(deftest match-4
    (comfy-6502::match '(a b . ?c) '(a b foo))
  t ((?c . (foo))))

(deftest match-5
    (comfy-6502::match '(a b . ?c) '(a b))
  t ((?c . nil)))

(deftest match-6
    (comfy-6502::match '(a b . ?c) '(a b foo bar))
  t ((?c . (foo bar))))

(deftest match-7
    (comfy-6502::match '(a ?v1 ?v2) '(a b c))
  t ((?v1 . b) (?v2 . c)))

(deftest match-8
    (comfy-6502::match '(a (?v1 . ?v2)) '(a (b . c)))
  t ((?v1 . b) (?v2 . c)))

(deftest match-9 
    (comfy-6502::match '(a (?v1 . ?v2)) '(a (b c d)))
  t ((?v1 . b) (?v2 . (c d))))
   
(deftest match-10
    (comfy-6502::match '(a (quote b) (:in evenp)) '(a b 6))
  T nil)

;; extension to allow capturing the value of tested variables
(deftest match-11
    (comfy-6502::match '(a (quote b) (:in evenp ?c)) '(a b 6))
  T ((?c . 6)))

(deftest match-12
    (comfy-6502::match '(a (quote b) (:in evenp ?c)) '(a b 7))
  nil nil)

;;; problematic...

(deftest match-13
    (comfy-6502::match '(a ?v1 ?v1) '(a b c))
  T ((?v1 . b) (?v1 . c)))

(deftest move-macro-1
    (comfy-macroexpand '(move (x) (y)))
  (seq (l x) (st y)))

(deftest move-macro-2
    (comfy-macroexpand '(move (i@ x) (@j y)))
  (seq (l i@ x) (st @j y)))

(deftest macro-1
    (progn
      (define-cmacro mac1
	((mac1 ?x ?y) (list ?y ?x)))
      (comfy-macroexpand '(mac1 a b)))
  (b a))

(deftest macro-2
    (progn
      (define-cmacro mac1
	((mac1 ?x ?y) (list ?y ?x)))
      (comfy-macroexpand '(mac1 (a c d) b)))
  (b (a c d)))

;;; define in one order [note: my define-cmacro has the reverse
;;; precedence from Baker's elisp implementation: the clauses are 
;;; matched sequentially, preferring the earlier clauses to laters.
;;; This matches Baker only if the (define cmacro ...) forms are 
;;; executed in the reverse order of the corresponding clauses, as
;;; (define cmacro ...) adds a new matcher to the beginning of the
;;; expander function.

(deftest macro-3
    (progn
      (define-cmacro mac2
	((mac2 ?x) (list 'match1 ?x))
	((mac2 ?x ?y) (list 'match2 ?x ?y))
	((mac2 ?x ?y . ?z) (list 'match3 ?x ?y ?z)))
      (list
       (comfy-macroexpand '(mac2 a))
       (comfy-macroexpand '(mac2 a b))
       (comfy-macroexpand '(mac2 a b c))))
  ((match1 a) (match2 a b) (match3 a b (c))))

(deftest macro-4
    (progn
      (define-cmacro mac2
	((mac2 ?x) (list 'match1 ?x))
	((mac2 ?x ?y . ?z) (list 'match3 ?x ?y ?z))
	((mac2 ?x ?y) (list 'match2 ?x ?y)))
      (list
       (comfy-macroexpand '(mac2 a))
       (comfy-macroexpand '(mac2 a b))
       (comfy-macroexpand '(mac2 a b c))))
  ((match1 a) (match3 a b nil) (match3 a b (c))))

(deftest symbol-macro-1
    (progn
      (define-cmacro fake-rr
	  (fake-rr '(7 rl))
	((fake-rr . ?x) (list 7 (cons 'rl ?x))))
      (list
       (comfy-macroexpand 'fake-rr)
       (comfy-macroexpand '(fake-rr loc))
       (comfy-macroexpand '(fake-rr i@ loc))))
  ((7 rl)
   (7 (rl loc))
   (7 (rl i@ loc))))

(deftest repeat-1
    (compile-code (3 (1+ 100)))
  ((INC :ZERO-PAGE) (:ZERO-PAGE 100) 
   (INC :ZERO-PAGE) (:ZERO-PAGE 100) 
   (INC :ZERO-PAGE) (:ZERO-PAGE 100)))

(deftest repeat-2
    (compile-code (3 rl))
  ((ROL) (ROL) (ROL)))

(deftest repeat-3
    (compile-code (3 (rl (:zero-page loc))))
  ((ROL :ZERO-PAGE) (:ZERO-PAGE LOC)
   (ROL :ZERO-PAGE) (:ZERO-PAGE LOC)
   (ROL :ZERO-PAGE) (:ZERO-PAGE LOC)))

(deftest rl-1 
    (compile-code (rl i@ (:zero-page loc)))
  ((ROL :ZP-X-INDIRECT) (:ZERO-PAGE LOC)))

(deftest repeat-4
    (compile-code (3 (rl i@ (:zero-page loc))))
  ((ROL :ZP-X-INDIRECT) (:ZERO-PAGE LOC)
   (ROL :ZP-X-INDIRECT) (:ZERO-PAGE LOC)
   (ROL :ZP-X-INDIRECT) (:ZERO-PAGE LOC)))

(deftest symbol-macro-2
    (progn
      (define-cmacro fake-rr
	  (fake-rr '(7 rl))
	((fake-rr . ?x) (list 7 (cons 'rl ?x))))
      (compile-code (seq fake-rr (fake-rr (:absolute loc)) 
			 (fake-rr i@ (:zero-page loc)))))
  ((ROL) (ROL) (ROL) (ROL) (ROL) (ROL) (ROL)
   (ROL :ABSOLUTE) (:ABSOLUTE LOC)
   (ROL :ABSOLUTE) (:ABSOLUTE LOC)
   (ROL :ABSOLUTE) (:ABSOLUTE LOC)
   (ROL :ABSOLUTE) (:ABSOLUTE LOC)
   (ROL :ABSOLUTE) (:ABSOLUTE LOC)
   (ROL :ABSOLUTE) (:ABSOLUTE LOC)
   (ROL :ABSOLUTE) (:ABSOLUTE LOC)
   (ROL :ZP-X-INDIRECT) (:ZERO-PAGE LOC)
   (ROL :ZP-X-INDIRECT) (:ZERO-PAGE LOC)
   (ROL :ZP-X-INDIRECT) (:ZERO-PAGE LOC)
   (ROL :ZP-X-INDIRECT) (:ZERO-PAGE LOC)
   (ROL :ZP-X-INDIRECT) (:ZERO-PAGE LOC)
   (ROL :ZP-X-INDIRECT) (:ZERO-PAGE LOC)
   (ROL :ZP-X-INDIRECT) (:ZERO-PAGE LOC)))

(deftest equ-1 
    (let ((comfy-6502::*symbol-table* (make-hash-table)))
      (equ n 32)
      (equ len 2)
      (compile-code (seq (ci \# len))))
  ((CPX :IMMEDIATE) (:byte 2)))

(deftest zp-1 
    (compile-code (l i 32))
  ((LDA :ZERO-PAGE-X) (:ZERO-PAGE 32)))

(deftest abs-1
    (compile-code (l i 256))
  ((LDA :ABSOLUTE-X) (:ABSOLUTE 256)))

(deftest lisp-1
	 (progn 
	   (defparameter *len* 2)
	   (compile-code (seq (ci \# (lisp *len*)))))
  ((CPX :IMMEDIATE) (:byte 2)))

(deftest equ-2
    (let ((comfy-6502::*symbol-table* (make-hash-table)))
      (equ n 32)
      (equ len 2)
      (compile-code (seq (l i n))))
  ((LDA :ZERO-PAGE-X) (:ZERO-PAGE 32)))

(deftest lisp-2
	 (progn 
	   (defparameter *n* 32)
	   (compile-code (seq (l i (lisp *n*)))))
  ((LDA :ZERO-PAGE-X) (:ZERO-PAGE 32)))

(deftest equ-3
    (let ((comfy-6502::*symbol-table* (make-hash-table)))
      (equ n 32)
      (equ len 2)
      (compile-code (seq (st i n))))
  ((STA :ZERO-PAGE-X) (:ZERO-PAGE 32)))

(deftest lisp-3
	 (progn 
	   (defparameter *n* 32)
	   (compile-code (seq (st i (lisp *n*)))))
  ((STA :ZERO-PAGE-X) (:ZERO-PAGE 32)))

(deftest compile-3-equ 
	(let ((comfy-6502::*symbol-table* (make-hash-table)))		 
	  (equ n 32)  ; address of counter
	  (equ len 2) ; number of bytes
	  (compile-code 
	    (seq (li \# 0)
		 c=1     ; initial (+ \# 0) will add 1
		 (while c=1?
			(seq (ci \# len)
			     LLT ; wins if X < #*len* unsign
			     (l i n) 
			     (+ \# 0) 
			     (st i n) 
			     i+1))) 
	    0 -10))
  ((LDX :IMMEDIATE) (:byte 0)    ;; [19] 
   (SEC)                 ;; [17]
   (BCC) (:BRANCH 15)    ;; [16] if done incrementing, WIN -> 0
   (CPX :IMMEDIATE) (:byte 2)    ;; [14]
   (BCS) (:BRANCH 21)    ;; [12] X>=#*len* means *n* overflowed: LOSE -> 110
   (LDA :ZERO-PAGE-X) (:ZERO-PAGE 32) ;; [10]
   (ADC :IMMEDIATE) (:byte 0)    ;; [8]
   (STA :ZERO-PAGE-X) (:ZERO-PAGE 32) ;; [6]
   (INX)                 ;; [4]
   (JMP :ABSOLUTE) (:LONG-BRANCH -14))) ;; [3]

;;; tests for "declaration" behavior: allow a value ':ZERO-PAGE or '(:ZERO-PAGE) or
;;; '(:ZERO-PAGE NIL) to emit a (:ZERO-PAGE <symbol>) address

(deftest zp-assert-1
    (compile-code (l i (:zero-page n)))
  ((LDA :ZERO-PAGE-X) (:ZERO-PAGE N)))

(deftest declare-1
    (let ((comfy-6502::*symbol-table* (make-hash-table)))
      (equ n :zero-page)
      (compile-code (seq (l i n))))
  ((LDA :ZERO-PAGE-X) (:ZERO-PAGE N)))

;;; test for catching various errors

(deftest zp-error-1
    (compile-code (l i 256))
  ((LDA :ABSOLUTE-X) (:ABSOLUTE 256)))

(deftest bad-if-1
    (multiple-value-bind (success error)
	(ignore-errors (compile-code (if =0?)))
      (list success (eq (class-of error) (find-class 'if-error))
	    (problem error)))
  (nil t "lacking win-form"))

(deftest bad-if-2
    (multiple-value-bind (success error)
	(ignore-errors (compile-code (if =0? return)))
      (list success (eq (class-of error) (find-class 'if-error))
	    (problem error)))
  (nil t "lacking lose-form"))

(deftest bad-if-3
    (multiple-value-bind (success error)
	(ignore-errors (compile-code (if)))
      (list success (eq (class-of error) (find-class 'if-error))
	    (problem error)))
  (nil t "lacking win-form"))

(deftest bad-if-4
    (multiple-value-bind (success error)
	(ignore-errors (compile-code (if test then else extra)))
      (list success (eq (class-of error) (find-class 'if-error))
	    (problem error)))
  (nil t "too many forms"))

(deftest bad-while-1
    (multiple-value-bind (success error)
	(ignore-errors (compile-code (while =0?)))
      (list success (eq (class-of error) (find-class 'while-error))
	    (problem error)))
  (nil t "lacking win-form"))

(deftest bad-while-2
    (multiple-value-bind (success error)
	(ignore-errors (compile-code (while)))
      (list success (eq (class-of error) (find-class 'while-error))
	    (problem error)))
  (nil t "lacking test-form"))

(deftest bad-while-3
    (multiple-value-bind (success error)
	(ignore-errors (compile-code (while a b c)))
      (list success (eq (class-of error) (find-class 'while-error))
	    (problem error)))
  (nil t "too many forms"))

(deftest bad-opcode-1
    (multiple-value-bind (success error)
	(ignore-errors (compile-code (if bogus-test? return
					 (1- 100))))
      (list success (eq (class-of error) (find-class 'opcode-error))
	    (problem error)))
  (nil t "not an implied opcode"))

(deftest bad-accum-1
    (multiple-value-bind (success error)
	(ignore-errors (compile-code (1+ a)))
      (list success (eq (class-of error) (find-class 'opcode-error))
	    (problem error)))
  (nil t "does not support ACCUMULATOR mode"))

(deftest bad-implied-1
    (multiple-value-bind (success error)
	(ignore-errors (compile-code INC))
      (list success (eq (class-of error) (find-class 'opcode-error))
	    (problem error)))
  (nil t "does not support IMPLIED mode"))


;;; example of Apple II "Red Book" tone routine.

(deftest redbook-tone
    (let ((comfy-6502::*symbol-table* (make-hash-table))
	  (comfy-6502::*optimize-loop-branches* nil))
      (equ speaker #xc030)
      (equ duration 1)
      (equ pitch 0)
      (comfy-6502-tests::compile-code
       (comfy-6502:loop 
	;; repeat until some clause loses: actually, only exit is
	;; through return, so each clause should be ensured of winning.
	(li pitch)
	(l speaker)
	(not (comfy-6502:loop  ;; repeat until whap time (pitch counter expires)
	      j-1
	      (if =0? ; duration tick finished?
		  (not (seq (1- duration) ; yes, count down duration
			    =0? ;; duration expired? 
			    ;; (failure skips return but seq protected by
			    ;; NOT to avoid exiting and WHAPping)
			    return))
		  (seq i-1 ~=0?))))))) ; no, continue counting pitch
  (; reload-pitch
   (LDX :ZERO-PAGE) (:ZERO-PAGE 0) 
   (LDA :ABSOLUTE) (:ABSOLUTE 49200) 
   ;; spin
   (DEY) 
   (BEQ) (:BRANCH 6) ; duration-tick
   (DEX) 
   (BNE) (:BRANCH 8) ; goto spin
   (BEQ) (:BRANCH 9) ; goto reload-pitch
   ;; duration-tick
   (DEC :ZERO-PAGE) (:ZERO-PAGE 1) 
   (BNE) (:BRANCH 2) ; goto-spin
   (RTS) 
   ;; goto spin
   (JMP :ABSOLUTE) (:LONG-BRANCH -14) 
   ;; goto reload-pitch
   (JMP :ABSOLUTE) (:LONG-BRANCH -22)))

;; with optimizations enabled

(deftest redbook-tone-opt-branches
    ;; redirect branches, but leave redundant JMPs
    (let ((comfy-6502::*symbol-table* (make-hash-table))
	  (comfy-6502::*excise-loop-jump* nil))
      (equ speaker #xc030)
      (equ duration 1)
      (equ pitch 0)
      (comfy-6502-tests::compile-code
       (comfy-6502:loop 
	;; repeat until some clause loses: actually, only exit is
	;; through return, so each clause should be ensured of winning.
	(li pitch)
	(l speaker)
	(not (comfy-6502:loop  ;; repeat until whap time (pitch counter expires)
	      j-1
	      (if =0? ; duration tick finished?
		  (not (seq (1- duration) ; yes, count down duration
			    =0? ;; duration expired? 
			    ;; (failure skips return but seq protected by
			    ;; NOT to avoid exiting and WHAPping)
			    return))
		  (seq i-1 ~=0?))))))) ; no, continue counting pitch
  (; reload-pitch
   (LDX :ZERO-PAGE) (:ZERO-PAGE 0) 
   (LDA :ABSOLUTE) (:ABSOLUTE 49200) 
   ;; spin
   (DEY) 
   (BEQ) (:BRANCH 6) ; duration-tick
   (DEX) 
   (BNE) (:BRANCH -5) ; SHORTENED spin
   (BEQ) (:BRANCH -12) ; SHORTENED reload-pitch
   ;; duration-tick
   (DEC :ZERO-PAGE) (:ZERO-PAGE 1) 
   (BNE) (:BRANCH -11) ; SHORTENED spin
   (RTS) 
   ;; goto spin
   (JMP :ABSOLUTE) (:LONG-BRANCH -14) ;; EXCISEABLE 
   ;; goto reload-pitch
   (JMP :ABSOLUTE) (:LONG-BRANCH -22))) ;; EXCISEABLE

(deftest redbook-tone-opt ; "full" optimizations
    ;; expected to fail under comfy-6502.lisp 1.9
    (let ((comfy-6502::*symbol-table* (make-hash-table)))
      (equ speaker #xc030)
      (equ duration 1)
      (equ pitch 0)
      (comfy-6502-tests::compile-code
       (comfy-6502:loop 
	;; repeat until some clause loses: actually, only exit is
	;; through return, so each clause should be ensured of winning.
	(li pitch)
	(l speaker)
	(not (comfy-6502:loop  ;; repeat until whap time (pitch counter expires)
	      j-1
	      (if =0? ; duration tick finished?
		  (not (seq (1- duration) ; yes, count down duration
			    =0? ;; duration expired? 
			    ;; (failure skips return but seq protected by
			    ;; NOT to avoid exiting and WHAPping)
			    return))
		  (seq i-1 ~=0?))))))) ; no, continue counting pitch
  (; reload-pitch
   (LDX :ZERO-PAGE) (:ZERO-PAGE 0) 
   (LDA :ABSOLUTE) (:ABSOLUTE 49200) 
   ;; spin
   (DEY) 
   (BEQ) (:BRANCH 6) ; duration-tick
   (DEX) 
   (BNE) (:BRANCH -5) ; SHORTENED spin
   (BEQ) (:BRANCH -12) ; SHORTENED reload-pitch
   ;; duration-tick
   (DEC :ZERO-PAGE) (:ZERO-PAGE 1) 
   (BNE) (:BRANCH -11) ; SHORTENED spin
   (RTS)))  ;; without JMP elimination, there are redundant
;; (JMP :ABSOLUTE) (:LONG-BRANCH -14)
;; (JMP :ABSOLUTE) (:LONG-BRANCH -22)

;; that one actually disagrees with the logic of the original
;;

(deftest redbook-tone-2
    (let ((comfy-6502::*symbol-table* (make-hash-table))
	  (comfy-6502::*optimize-loop-branches* nil))
      (equ speaker #xc030)
      (equ duration 1)
      (equ pitch 0)
      (comfy-6502-tests::compile-code
       (alt (loop (seq (li pitch) (l speaker)) 
	       (not (while 
			(seq j-1 (not (seq =0? (1- duration) =0?)))
		      (seq i-1 (not =0?)))))
	    return)))
  (; reload
    (LDX :ZERO-PAGE) (:ZERO-PAGE 0) 
    (LDA :ABSOLUTE) (:ABSOLUTE 49200) 
    ; spin
    (DEY) 
    (BNE) (:BRANCH 5) ; not-duration
    ; duration-tick
    (DEC :ZERO-PAGE) (:ZERO-PAGE 1) 
    (BEQ) (:BRANCH 10) ; exit
    ; not-duration
    (DEX) 
    (BEQ) (:BRANCH 4) ; goto-reload
    ; goto-spin
    (JMP :ABSOLUTE) (:LONG-BRANCH -11) 
    ; goto-reload
    (JMP :ABSOLUTE) (:LONG-BRANCH -19) ; reload
    ; exit
    (RTS)))

(deftest redbook-tone-2-opt
    (let ((comfy-6502::*symbol-table* (make-hash-table)))
      (equ speaker #xc030)
      (equ duration 1)
      (equ pitch 0)
      (comfy-6502-tests::compile-code
       (alt (loop (seq (li pitch) (l speaker)) 
	       (not (while 
			(seq j-1 (not (seq =0? (1- duration) =0?)))
		      (seq i-1 (not =0?)))))
	    return)))
  (; reload
    (LDX :ZERO-PAGE) (:ZERO-PAGE 0) 
    (LDA :ABSOLUTE) (:ABSOLUTE 49200) 
    ; spin
    (DEY) 
    (BNE) (:BRANCH 5) ; not-duration
    ; duration-tick
    (DEC :ZERO-PAGE) (:ZERO-PAGE 1) 
    (BEQ) (:BRANCH 10) ; exit
    ; not-duration
    (DEX) 
    (BEQ) (:BRANCH -14) ; SHORTENED reload
    ; goto-spin
    (JMP :ABSOLUTE) (:LONG-BRANCH -11) 
    ; goto-reload
    (JMP :ABSOLUTE) (:LONG-BRANCH -19) ; reload
    ; exit
    (RTS)))
      

;;; test "conventional" aliases: 6502 instruction names

;; cf. compile-1
(deftest alias-1 (compile-code (seq CLC CLV CLD SED CLI SEI)) 
  ((CLC) (CLV) (CLD) (SED) (CLI) (SEI)))

;; cf. compile-2
(deftest alias-2 (compile-code (not (loop TSX (not zero?) PLA)))
  ;; clear the stack
  ((TSX) (BEQ) (:BRANCH 5) (PLA) (JMP :ABSOLUTE) (:LONG-BRANCH -5)))

;; cf. compile-3
(deftest alias-3 (progn
		   (defparameter *n* 32)  ; address of counter
		   (defparameter *len* 2) ; number of bytes
		   (compile-code (seq (LDX \# 0)
				      SEC     ; initial (ADC \# 0) will add 1
				      (while carry?
					(seq (CPX \# (lisp *len*))
					     LLT ; wins if X < #*len* unsign
					     (LDA X (lisp *n*))
					     (ADC \# 0) 
					     (STA X (lisp *n*)) 
					     INX))) 
				 0 -10))
  ((LDX :IMMEDIATE) (:BYTE 0)    ;; [19] 
   (SEC)                 ;; [17]
   (BCC) (:BRANCH 15)    ;; [16] if done incrementing, WIN -> 0
   (CPX :IMMEDIATE) (:BYTE 2)    ;; [14]
   (BCS) (:BRANCH 21)    ;; [12] X>=#*len* means *n* overflowed: LOSE -> 110
   (LDA :ZERO-PAGE-X) (:ZERO-PAGE 32) ;; [10]
   (ADC :IMMEDIATE) (:BYTE 0)    ;; [8]
   (STA :ZERO-PAGE-X) (:ZERO-PAGE 32) ;; [6]
   (INX)                 ;; [4]
   (JMP :ABSOLUTE) (:LONG-BRANCH -14))) ;; [3]

;; cf. redbook-tone-2
(deftest redbook-2-alias
    (let ((comfy-6502::*symbol-table* (make-hash-table))
	  (comfy-6502::*optimize-loop-branches* nil))
      (equ speaker #xc030)
      (equ duration 1)
      (equ pitch 0)
      (comfy-6502-tests::compile-code
       (alt (loop (seq (LDX pitch) (LDA speaker)) 
	       (not (while 
			(seq DEY (not (seq zero? (DEC duration) zero?)))
		      (seq DEX (not zero?)))))
	    RTS)))
  (; reload
    (LDX :ZERO-PAGE) (:ZERO-PAGE 0) 
    (LDA :ABSOLUTE) (:ABSOLUTE 49200) 
    ; spin
    (DEY) 
    (BNE) (:BRANCH 5) ; not-duration
    ; duration-tick
    (DEC :ZERO-PAGE) (:ZERO-PAGE 1) 
    (BEQ) (:BRANCH 10) ; exit
    ; not-duration
    (DEX) 
    (BEQ) (:BRANCH 4) ; goto-reload
    ; goto-spin
    (JMP :ABSOLUTE) (:LONG-BRANCH -11) 
    ; goto-reload
    (JMP :ABSOLUTE) (:LONG-BRANCH -19) ; reload
    ; exit
    (RTS)))

(deftest redbook-2-alias-opt
    (let ((comfy-6502::*symbol-table* (make-hash-table)))
      (equ speaker #xc030)
      (equ duration 1)
      (equ pitch 0)
      (comfy-6502-tests::compile-code
       (alt (loop (seq (LDX pitch) (LDA speaker)) 
	       (not (while 
			(seq DEY (not (seq zero? (DEC duration) zero?)))
		      (seq DEX (not zero?)))))
	    RTS)))
  (; reload
    (LDX :ZERO-PAGE) (:ZERO-PAGE 0) 
    (LDA :ABSOLUTE) (:ABSOLUTE 49200) 
    ; spin
    (DEY) 
    (BNE) (:BRANCH 5) ; not-duration
    ; duration-tick
    (DEC :ZERO-PAGE) (:ZERO-PAGE 1) 
    (BEQ) (:BRANCH 10) ; exit
    ; not-duration
    (DEX) 
    (BEQ) (:BRANCH -14) ; SHORTENED reload
    ; goto-spin
    (JMP :ABSOLUTE) (:LONG-BRANCH -11) 
    ; goto-reload
    (JMP :ABSOLUTE) (:LONG-BRANCH -19) ; reload
    ; exit
    (RTS)))

;; cf. zp-1
(deftest alias-4
    (compile-code (LDA X 32))
  ((LDA :ZERO-PAGE-X) (:ZERO-PAGE 32)))

;; cf. equ-1
(deftest alias-5
    (let ((comfy-6502::*symbol-table* (make-hash-table)))
      (equ n 32)
      (equ len 2)
      (compile-code (CPX \# len)))
  ((CPX :IMMEDIATE) (:byte 2)))

;; cf. equ-3
(deftest alias-6
    (let ((comfy-6502::*symbol-table* (make-hash-table)))
      (equ n 32)
      (equ len 2)
      (compile-code (STA X n)))
  ((STA :ZERO-PAGE-X) (:ZERO-PAGE 32)))

;; cf. repeat-1
(deftest alias-7
    (compile-code (2 (INC 100)))
  ((INC :ZERO-PAGE) (:ZERO-PAGE 100) 
   (INC :ZERO-PAGE) (:ZERO-PAGE 100)))

;; cf. repeat-2
(deftest alias-8 
    (compile-code (3 ROL))
  ((ROL) (ROL) (ROL)))

;; cf rl-1
(deftest alias-9
    (compile-code (ROL X@ (:zero-page loc)))
  ((ROL :ZP-X-INDIRECT) (:ZERO-PAGE LOC)))

;;; try out some of the example macros that need address math

(deftest i2-1
    (compile-code (comfy-6502::i2 99))
  ((INC :ZERO-PAGE) (:ZERO-PAGE 99) 
   (BNE) (:BRANCH 3) 
   (INC :ZERO-PAGE) (:ZERO-PAGE 100)))

(deftest i2-2
    (compile-code (comfy-6502::i2 255))
  ((INC :ZERO-PAGE) (:ZERO-PAGE 255) 
   (BNE) (:BRANCH 4) 
   (INC :ABSOLUTE) (:ABSOLUTE 256)))

(deftest i2-3
    (compile-code (comfy-6502::i2 1000))
  ((INC :ABSOLUTE) (:ABSOLUTE 1000) 
   (BNE) (:BRANCH 4) 
   (INC :ABSOLUTE) (:ABSOLUTE 1001)))

;;; not sure if I like this behavior.
(deftest i2-4
    (compile-code (comfy-6502::i2 -1))
  ((INC :ABSOLUTE) (:ABSOLUTE -1) 
   (BNE) (:BRANCH 3) 
   (INC :ZERO-PAGE) (:ZERO-PAGE 0)))

#|| ; doesn't work yet
(deftest i2-5
    (compile-code (comfy-6502::i2 (:ABSOLUTE x)))
  ((INC :ABSOLUTE) (:ABSOLUTE X) 
   (BNE) (:BRANCH 4) 
   (INC :ABSOLUTE) (:ABSOLUTE (1+ (:ABSOLUTE X))))) ; or something like this.
||#

;; some aliases not used in Baker's examples, but that work with
;; his original code.
;; (li a) -> 170 decimal = TAX, (sti a) -> 138 decimal = TXA
;; (lj a) -> 168 decimal = TAY, (stj a) -> 152 decimal = TYA
;; 

(deftest alias-accum
    (compile-code (seq (li a) (sti a) (lj a) (stj a)
		       (LDX A) (STX A) (LDY A) (STY A)))
  ((TAX) (TXA) (TAY) (TYA) (TAX) (TXA) (TAY) (TYA)))

(deftest null-loop ; make sure optimizer doesn't choke on this.
    (compile-code (loop))
  ((JMP :ABSOLUTE) (:LONG-BRANCH -1)))
