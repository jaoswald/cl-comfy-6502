;;;; -*- mode: Lisp; Syntax: ANSI-Common-Lisp; Package: ("6502-TESTS" ("CL" "6502" "RT")); -*-
;;;;
;;;; 6502-tests.lisp
;;;;
;;;; Uses RT regression test framework

(cl:defpackage "6502-TESTS"
  (:use "COMMON-LISP" "6502" #+sbcl "SB-RT" #-sbcl "RT"))

(in-package "6502-TESTS")

(defmacro def-branch-test (instruction opcode)
  "Define a test for a branch instruction (a symbol) which has
the specified numeric opcode."
  (let ((base-name (symbol-name instruction))
	(sym instruction)
	(code opcode))
    `(progn
       (deftest ,(make-symbol (concatenate 'string base-name "-test-1"))
	   (opcode-to-byte (make-symbolic-opcode ',sym :BRANCH-RELATIVE)) 
	 ,code)
       (deftest ,(make-symbol (concatenate 'string base-name "-test-2"))
	   (opcode-to-byte (make-symbolic-opcode ',sym nil))
	 ,code)
       (deftest ,(make-symbol (concatenate 'string base-name "-test-3"))
	   (handler-case 
	       (opcode-to-byte (make-symbolic-opcode ',sym :IMMEDIATE))
	     (bad-address-mode () :pass)
	     (error () :unexpected-error)
	     (:no-error () :no-error))
	 :pass)
       (deftest ,(make-symbol (concatenate 'string base-name "-test-4"))
	   (handler-case 
	       (opcode-to-byte (make-symbolic-opcode ',sym :BOGUS))
	     (bad-address-mode () :pass)
	     (error () :unexpected-error)
	     (:no-error () :no-error))
	 :pass))))


(def-branch-test BCC 144)
(def-branch-test BCS 176)
(def-branch-test BEQ 240)
(def-branch-test BNE 208)
(def-branch-test BVS 112)
(def-branch-test BVC 80)
(def-branch-test BMI 48)
(def-branch-test BPL 16)

;;; RT apparently doesn't support "suites" of tests

#||
(build-suite "branch-suite" 
     "BCC-test" "BCS-test"
     "BEQ-test" "BNE-test"
     "BVS-test" "BVC-test"
     "BMI-test" "BPL-test")
||#  

(defmacro def-implied-test (instruction opcode)
  "Define a test for an implied-address-mode instruction (a symbol) which has
the specified numeric opcode."
  (let ((base-name (symbol-name instruction))
	(sym instruction)
	(code opcode))
    `(progn
       (deftest ,(make-symbol (concatenate 'string base-name "-test-1"))
	   (opcode-to-byte (make-symbolic-opcode ',sym :IMPLIED))
	 ,code)
       (deftest ,(make-symbol (concatenate 'string base-name "-test-2"))
	   (opcode-to-byte (make-symbolic-opcode ',sym nil))
	 ,code)
       (deftest ,(make-symbol (concatenate 'string base-name "-test-3"))
	   (handler-case 
	       (opcode-to-byte (make-symbolic-opcode ',sym :BRANCH-RELATIVE))
	     (bad-address-mode () :pass)
	     (error () :unexpected-error)
	     (:no-error () :no-error))
	 :pass)
       (deftest ,(make-symbol (concatenate 'string base-name "-test-4"))
	   (handler-case 
	       (opcode-to-byte (make-symbolic-opcode ',sym :IMMEDIATE))
	     (bad-address-mode () :pass)
	     (error () :unexpected-error)
	     (:no-error () :no-error))
	 :pass)
       (deftest ,(make-symbol (concatenate 'string base-name "-test-5"))
	   (handler-case 
	       (opcode-to-byte (make-symbolic-opcode ',sym :BOGUS))
	     (bad-address-mode () :pass)
	     (error () :unexpected-error)
	     (:no-error () :no-error))
	 :pass))))

(def-implied-test BRK 0)
(def-implied-test NOP 234)
(def-implied-test PHP 8)
(def-implied-test PLP 40)
(def-implied-test PHA 72)
(def-implied-test PLA 104)
(def-implied-test CLC 24)
(def-implied-test SEC 56)
(def-implied-test CLV 184)
(def-implied-test CLI 88)
(def-implied-test SEI 120)
(def-implied-test CLD 216)
(def-implied-test SED 248)
(def-implied-test DEX 202)
(def-implied-test DEY 136)
(def-implied-test INX 232)
(def-implied-test INY 200)
(def-implied-test RTS 96)
(def-implied-test RTI 64)
(def-implied-test TAX 170)
(def-implied-test TXA 138)
(def-implied-test TAY 168)
(def-implied-test TYA 152)
(def-implied-test TXS 154)
(def-implied-test TSX 186)

#||
(build-suite "implied-suite"
     "NOP-test" "BRK-test" 
     "PHP-test" "PLP-test"
     "PHA-test" "PLA-test"
     "CLC-test" "SEC-test"
     "CLI-test" "SEI-test"
     "CLD-test" "SED-test"
     "CLV-test" 
     "INX-test" "DEX-test" 
     "INY-test" "DEY-test"
     "RTS-test" "RTI-test" 
     "TXA-test" "TAX-test" 
     "TYA-test" "TAY-test"
     "TXS-test" "TSX-test")
||#

;;; opcodes with multiple valid address modes
;;; define arbitrary order
;;; accumulator, immediate, absolute absolute-x absolute-y
;;; zero-page, zero-page-x, zp-x-indirect, zp-indirect-y
;;; absolute-indirect
;;; numeric means valid opcode, nil means address-mode disallowed

;;; FIXME: add assert-error for BRANCH-RELATIVE, IMPLIED, nil address-mode

(defmacro def-opcode-test (instruction acc imm abs abs-x abs-y
			   zp zp-x zp-x-ind zp-y zp-ind-y
			   abs-ind)
  (let ((base-name (symbol-name instruction))
	(sym instruction)
	(test-counter 0))
    `(progn
       ,@(mapcar (function (lambda (opcode am)
		   `(deftest ,(make-symbol 
			       (concatenate 'string  
					    base-name "-test" 
					    (princ-to-string 
					     (incf test-counter))))
			,@(if opcode 
			      (list 
			       `(opcode-to-byte (make-symbolic-opcode
						 ',sym ,am))
			       opcode)
			      (list
			       `(handler-case 
				    (opcode-to-byte (make-symbolic-opcode 
						     ',sym ,am))
				  (bad-address-mode () :pass)
				  (error () :unexpected-error)
				  (:no-error () :no-error))
			       :pass)))))
		 (list acc imm
		       abs abs-x abs-y 
		       zp zp-x zp-x-ind zp-y zp-ind-y 
		       abs-ind)
		 '(:ACCUMULATOR :IMMEDIATE
		   :ABSOLUTE :ABSOLUTE-X :ABSOLUTE-Y
		   :ZERO-PAGE :ZERO-PAGE-X 
		   :ZP-X-INDIRECT 
		   :ZERO-PAGE-Y :ZP-INDIRECT-Y 
		   :ABSOLUTE-INDIRECT)))))

;;                    acc imm abs abs-x abs-y zp zp-x zp-x-ind zp-y zp-ind-y abs-ind

(def-opcode-test STA  nil nil 141  157   153  133 149    129   nil   145   nil)
(def-opcode-test LDA  nil 169 173  189   185  165 181    161   nil   177   nil)
(def-opcode-test ORA  nil   9  13   29    25    5  21      1   nil    17   nil)
(def-opcode-test ADC  nil 105 109  125   121  101 117     97   nil   113   nil)
(def-opcode-test SBC  nil 233 237  253   249  229 245    225   nil   241   nil)
(def-opcode-test EOR  nil  73  77   93    89   69  85     65   nil    81   nil)
(def-opcode-test CMP  nil 201 205  221   217  197 213    193   nil   209   nil)
(def-opcode-test AND  nil  41  45   61    57   37  53     33   nil    49   nil)

#||
(build-suite "accum-suite"
     "STA-test" "LDA-test"
     "ADC-test" "SBC-test"
     "ORA-test" "EOR-test" "AND-test" 
     "CMP-test")
||#

;;                    acc imm abs abs-x abs-y zp zp-x zp-x-ind zp-y zp-ind-y abs-ind
(def-opcode-test ASL   10 nil  14   30   nil   6   22    nil   nil   nil   nil)
(def-opcode-test LSR   74 nil  78   94   nil  70   86    nil   nil   nil   nil)
(def-opcode-test ROR  106 nil 110  126   nil 102  118    nil   nil   nil   nil)
(def-opcode-test ROL   42 nil  46   62   nil  38   54    nil   nil   nil   nil)

#||
(build-suite "rotate-suite"
     "ASL-test" "LSR-test"
     "ROL-test" "ROR-test")
||#

;;                    acc imm abs abs-x abs-y zp zp-x zp-x-ind zp-y zp-ind-y abs-ind
(def-opcode-test INC  nil nil 238  254   nil 230  246    nil   nil   nil   nil)
(def-opcode-test DEC  nil nil 206  222   nil 198  214    nil   nil   nil   nil)

(def-opcode-test BIT  nil nil  44  nil   nil  36  nil    nil   nil   nil   nil)

#||
(build-suite "inc/dec/bit-suite"
     "INC-test"
     "DEC-test"
     "BIT-test")
||#

;;                    acc imm abs abs-x abs-y zp zp-x zp-x-ind zp-y zp-ind-y abs-ind
(def-opcode-test JMP  nil nil  76  nil   nil nil  nil    nil   nil   nil   108)
(def-opcode-test JSR  nil nil  32  nil   nil nil  nil    nil   nil   nil   nil)

#||
(build-suite "jump-suite"
     "JSR-test"
     "JMP-test")
||#

;;                    acc imm abs abs-x abs-y zp zp-x zp-x-ind zp-y zp-ind-y abs-ind
(def-opcode-test LDX  nil 162 174  nil   190 166  nil    nil   182   nil   nil)
(def-opcode-test STX  nil nil 142  nil   nil 134  nil    nil   150   nil   nil)
(def-opcode-test LDY  nil 160 172  188   nil 164  180    nil   nil   nil   nil)
(def-opcode-test STY  nil nil 140  nil   nil 132  148    nil   nil   nil   nil)

(def-opcode-test CPX  nil 224 236  nil   nil 228  nil    nil   nil   nil   nil)
(def-opcode-test CPY  nil 192 204  nil   nil 196  nil    nil   nil   nil   nil)

#||
(build-suite "index-suite"
     "LDX-test" "LDY-test"
     "STX-test" "STY-test"
     "CPX-test" "CPY-test")
||#

#||
;; used by suites, unless the suite is built again.

;; suite-of-suites, requires modifications to elk-test.el

(build-suite "6502-opcode-suite" 
     "branch-suite" "implied-suite" "accum-suite" "rotate-suite"
     "inc/dec/bit-suite" "jump-suite" "index-suite")

||#

