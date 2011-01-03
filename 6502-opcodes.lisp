;;;; -*- mode: Lisp; Package: ("6502" "CL"); Syntax: ANSI-Common-Lisp; -*-
;;;;
;;;; 6502-opcodes.lisp
;;;
;;;

;;; basic operations on 6502 machine instructions.

;;; representation for Common Lisp
;;; a 'symbolic opcode' is (opcode address-mode)
;;; such as ('BCS 'BRANCH-RELATIVE)

;;; error conditions

(cl:defpackage "6502" 
	       (:use "CL")
	       (:export "6502-ERROR" "BAD-ADDRESS-MODE" "BAD-OPCODE"
			"OPCODE" "ADDRESS-MODE" "SYMBOLIC-OPCODE"
			"MAKE-SYMBOLIC-OPCODE" "OPCODE-TO-BYTE"
			"ADC" "AND" "ASL" 
			"BCC" "BCS" "BEQ" "BIT" "BMI" "BNE" "BPL" "BRK" "BVC" "BVS"
			"CLC" "CLD" "CLI" "CLV" "CMP" "CPX" "CPY" 
			"DEC" "DEX" "DEY"
			"EOR" 
			"INC" "INX" "INY"
			"JMP" "JSR"
			"LDA" "LDX" "LDY" "LSR"
			"NOP"
			"ORA"
			"PHA" "PHP" "PLA" "PLP"
			"ROL" "ROR" "RTI" "RTS"
			"SBC" "SEC" "SED" "SEI" "STA" "STX" "STY"
			"TAX" "TAY" "TSX" "TXA" "TXS" "TYA"))

(in-package "6502")

; (defgeneric address-mode (object)) 
; (defgeneric (setf address-mode) (value object))

; Genera 8.3 will otherwise define these as Flavor accessors in define-condition,
; causing a conflict when defclass symbolic-opcode later defines them as
; CLOS generic functions


(define-condition 6502-error (error) ())

(define-condition bad-address-mode (6502-error) 
  ((mnemonic :reader error-mnemonic :initarg :mnemonic)
   (address-mode :reader error-address-mode :initarg :address-mode))
  (:report (lambda (condition stream)
	     (format stream "~A does not support ~A address mode."
		     (error-mnemonic condition)
		     (error-address-mode condition)))))

(define-condition bad-opcode (6502-error) 
  ((mnemonic :reader error-mnemonic :initarg :mnemonic))
  (:report (lambda (condition stream)
	     (format stream "~A is not a valid 6502 mnemonic"
		     (error-mnemonic condition)))))


;;; 6502 machine code primitives

(defclass symbolic-opcode ()
  ((address-mode :initarg :address-mode :accessor address-mode)
   (opcode :initarg :opcode :accessor opcode)))

(defun make-symbolic-opcode (opcode address-mode)
  (unless (member address-mode
		  '(nil :BRANCH-RELATIVE :IMMEDIATE :ACCUMULATOR
			:IMPLIED :ABSOLUTE :ABSOLUTE-INDIRECT
			:ZERO-PAGE
			:ZERO-PAGE-X :ABSOLUTE-X :ZERO-PAGE-Y
			:ZP-X-INDIRECT :ZP-INDIRECT-Y :ABSOLUTE-Y))
    (error 'bad-address-mode :mnemonic opcode 
	   :address-mode address-mode))
  (make-instance 'symbolic-opcode :opcode opcode :address-mode address-mode))

(defparameter *opcode-print-mode* :DEFAULT)

(defmethod print-object ((obj symbolic-opcode) stream)
  (case *opcode-print-mode*
    (:DEFAULT (print-unreadable-object (obj stream)
		(case (address-mode obj)
		  ((:BRANCH-RELATIVE :IMPLIED) (format stream "~A" (opcode obj)))
		  (t (format stream "~A ~A" (opcode obj) (address-mode obj))))))
    (t (format stream obj))))

(defvar +branch-opcodes+ '(BCS BCC BEQ BNE BVS BVC BMI BPL))

(setf (get 'BCS 'opcode) 176)
(setf (get 'BCC 'opcode) 144)
(setf (get 'BEQ 'opcode) 240)
(setf (get 'BNE 'opcode) 208)
(setf (get 'BVS 'opcode) 112)
(setf (get 'BVC 'opcode) 80)
(setf (get 'BMI 'opcode) 48)
(setf (get 'BPL 'opcode) 16)


(defun branch-opcode-to-byte (symbolic-opcode)
  (let ((op (opcode symbolic-opcode))
	(am (address-mode symbolic-opcode)))
    (unless (or (null am) (eq am :BRANCH-RELATIVE))
      (error 'bad-address-mode :mnemonic op :address-mode am))
    (if (member op +branch-opcodes+)
	(get op 'opcode)
	(error 'bad-opcode :mnemonic op))))

(defvar +implied-opcodes+ '(NOP BRK PHP PHA PLA PLP CLC SEC CLI SEI CLD SED CLV
				INX INY DEX DEY RTS RTI TXA TAX TYA TAY TXS TSX))

(setf (get 'BRK 'opcode) 0)
(setf (get 'NOP 'opcode) 234)
(setf (get 'PHP 'opcode) 8)
(setf (get 'PLP 'opcode) 40)
(setf (get 'PHA 'opcode) 72)
(setf (get 'PLA 'opcode) 104)
(setf (get 'CLC 'opcode) 24)
(setf (get 'SEC 'opcode) 56)
(setf (get 'CLV 'opcode) 184)
(setf (get 'CLI 'opcode) 88)
(setf (get 'SEI 'opcode) 120)
(setf (get 'CLD 'opcode) 216)
(setf (get 'SED 'opcode) 248)
(setf (get 'DEX 'opcode) 202)
(setf (get 'DEY 'opcode) 136)
(setf (get 'INX 'opcode) 232)
(setf (get 'INY 'opcode) 200)
(setf (get 'RTS 'opcode) 96)
(setf (get 'RTI 'opcode) 64)
(setf (get 'TAX 'opcode) 170)
(setf (get 'TXA 'opcode) 138)
(setf (get 'TAY 'opcode) 168)
(setf (get 'TYA 'opcode) 152)
(setf (get 'TXS 'opcode) 154)
(setf (get 'TSX 'opcode) 186)

(defun implied-opcode-to-byte (symbolic-opcode)
  (let ((op (opcode symbolic-opcode))
	(am (address-mode symbolic-opcode)))
    (unless (or (null am) (eq am :IMPLIED))
      (error 'bad-address-mode :mnemonic op :address-mode am))
    (if (member op +implied-opcodes+)
	(get op 'opcode)
	(error 'bad-opcode :mnemonic op))))
  
;;; "accumulator" instructions
;;; accumulator is an implied argument, allows 
;;; immediate, absolute, absolute,x, absolute,y
;;; zero-page, zero-page,x
;;; (zero-page,x) (zero-page),y 
;;;
;;; special case: STA immediate is invalid (acts as a NOP)

(defvar +accumulator-opcodes+ '(ORA AND EOR ADC STA LDA CMP SBC))

;; "basic" opcode for accumulator is ABSOLUTE

(setf (get 'STA 'opcode) 141)
(setf (get 'LDA 'opcode) 173)
(setf (get 'ORA 'opcode) 13)
(setf (get 'ADC 'opcode) 109)
(setf (get 'SBC 'opcode) 237)
(setf (get 'EOR 'opcode) 77)
(setf (get 'CMP 'opcode) 205)
(setf (get 'AND 'opcode) 45)

(defun accumulator-opcode-to-byte (symbolic-opcode)
  (let ((op (opcode symbolic-opcode))
	(am (address-mode symbolic-opcode)))
    (unless (member op +accumulator-opcodes+)
      (error 'bad-opcode :mnemonic op))
    (unless am
      (error 'bad-address-mode :mnemonic op :address-mode am))
    (let ((skel (get op 'opcode)))
      (unless skel (error "Missing 6502:OPCODE property on ~A" op))
      (cond 
	((eq am :IMMEDIATE)
	 (when (eq op 'STA)
	   (error 'bad-address-mode :mnemonic op :address-mode am))
	 (- skel 4))
	((eq am :ABSOLUTE)      skel)
	((eq am :ABSOLUTE-X)    (+ skel 16))
	((eq am :ABSOLUTE-Y)    (+ skel 12))
	((eq am :ZERO-PAGE)     (- skel 8))
	((eq am :ZERO-PAGE-X)   (+ skel 8))
	((eq am :ZP-X-INDIRECT) (- skel 12))
	((eq am :ZP-INDIRECT-Y) (+ skel 4))
	(t (error 'bad-address-mode :mnemonic op :address-mode am))))))


;; shift/rotate opcodes
;; can act on accumulator *or* memory
;; accumulator, absolute, absolute-x, zero-page, zero-page-x
;; for convenience, probably should not require explicit ACCUMULATOR
;; address mode, but will for now

(defvar +shift/rotate-opcodes+ '(ASL LSR ROL ROR))

;; "base" opcode is absolute

(setf (get 'ASL 'opcode) 14)
(setf (get 'LSR 'opcode) 78)
(setf (get 'ROL 'opcode) 46)
(setf (get 'ROR 'opcode) 110)

(defun shift/rotate-opcode-to-byte (symbolic-opcode)
  (let ((op (opcode symbolic-opcode))
	(am (address-mode symbolic-opcode)))
    (unless (member op +shift/rotate-opcodes+)
      (error 'bad-opcode :mnemonic op))
    (unless am
      (error 'bad-address-mode :mnemonic op :address-mode am))
    (let ((skel (get op 'opcode)))
      (unless skel (error "Missing OPCODE property on ~A" op))
      (cond 
	((eq am :ABSOLUTE)      skel)
	((eq am :ACCUMULATOR)   (- skel 4))
	((eq am :ABSOLUTE-X)    (+ skel 16))
	((eq am :ZERO-PAGE)     (- skel 8))
	((eq am :ZERO-PAGE-X)   (+ skel 8))
	(t (error 'bad-address-mode :mnemonic op :address-mode am))))))


;; inc/dec opcodes
;; can act only on memory
;; absolute, absolute-x, zero-page, zero-page-x
;; for convenience, probably should not require explicit ACCUMULATOR
;; address mode, but will for now

(defvar +inc/dec-opcodes+ '(INC DEC))

;; "base" opcode is absolute

(setf (get 'INC 'opcode) 238)
(setf (get 'DEC 'opcode) 206)

(defun inc/dec-opcode-to-byte (symbolic-opcode)
  (let ((op (opcode symbolic-opcode))
	(am (address-mode symbolic-opcode)))
    (unless (member op +inc/dec-opcodes+)
      (error 'bad-opcode :mnemonic op))
    (unless am
      (error 'bad-address-mode :mnemonic op :address-mode am))
    (let ((skel (get op 'opcode)))
      (unless skel (error "Missing OPCODE property on ~A" op))
      (cond 
	((eq am :ABSOLUTE)      skel)
	((eq am :ABSOLUTE-X)    (+ skel 16))
	((eq am :ZERO-PAGE)     (- skel 8))
	((eq am :ZERO-PAGE-X)   (+ skel 8))
	(t (error 'bad-address-mode :mnemonic op :address-mode am))))))

(setf (get 'BIT 'opcode) 44)

;; BIT only zero-page, absolute

(defun bit-opcode-to-byte (symbolic-opcode)
  (let ((op (opcode symbolic-opcode))
	(am (address-mode symbolic-opcode)))
    (unless (eq op 'BIT)
      (error 'bad-opcode :mnemonic op))
    (unless am
      (error 'bad-address-mode :mnemonic op :address-mode am))
    (let ((skel (get op 'opcode)))
      (unless skel (error "Missing OPCODE property on ~A" op))
      (cond 
	((eq am :ABSOLUTE)      skel)
	((eq am :ZERO-PAGE)     (- skel 8))
	(t (error 'bad-address-mode :mnemonic op :address-mode am))))))


;;; JMP only absolute, indirect

(setf (get 'JMP 'opcode) 76)

(defun jmp-opcode-to-byte (symbolic-opcode)
  (let ((op (opcode symbolic-opcode))
	(am (address-mode symbolic-opcode)))
    (unless (eq op 'JMP)
      (error 'bad-opcode :mnemonic op))
    (unless am
      (error 'bad-address-mode :mnemonic op :address-mode am))
    (let ((skel (get op 'opcode)))
      (unless skel (error "Missing OPCODE property on ~A" op))
      (cond 
	((eq am :ABSOLUTE)          skel)
	((eq am :ABSOLUTE-INDIRECT) (+ skel 32))
	(t (error 'bad-address-mode :mnemonic op :address-mode am))))))

;;; JSR only absolute

(setf (get 'JSR 'opcode) 32)

(defun jsr-opcode-to-byte (symbolic-opcode)
  (let ((op (opcode symbolic-opcode))
	(am (address-mode symbolic-opcode)))
    (unless (eq op 'JSR)
      (error 'bad-opcode :mnemonic op))
    (unless am
      (error 'bad-address-mode :mnemonic op :address-mode am))
    (let ((skel (get op 'opcode)))
      (unless skel (error "Missing OPCODE property on ~A" op))
      (cond 
	((eq am :ABSOLUTE)          skel)
	(t (error 'bad-address-mode :mnemonic op :address-mode am))))))

;;; index register opcodes
;; cpx, cpy, stx, sty, ldx, ldy

(defvar +compare-index-opcodes+ '(CPX CPY))

(setf (get 'CPX 'opcode) 236)
(setf (get 'CPY 'opcode) 204)

(defun compare-index-opcode-to-byte (symbolic-opcode)
  (let ((op (opcode symbolic-opcode))
	(am (address-mode symbolic-opcode)))
    (unless (member op +compare-index-opcodes+)
      (error 'bad-opcode :mnemonic op))
    (unless am
      (error 'bad-address-mode :mnemonic op :address-mode am))
    (let ((skel (get op 'opcode)))
      (unless skel (error "Missing OPCODE property on ~A" op))
      (cond 
	((eq am :ABSOLUTE)  skel)
	((eq am :IMMEDIATE) (- skel 12))
	((eq am :ZERO-PAGE) (- skel 8))
	(t (error 'bad-address-mode :mnemonic op :address-mode am))))))

(defvar +store-index-opcodes+ '(STX STY))

(setf (get 'STX 'opcode) 142)
(setf (get 'STY 'opcode) 140)

(defun store-index-opcode-to-byte (symbolic-opcode)
  (let ((op (opcode symbolic-opcode))
	(am (address-mode symbolic-opcode)))
    (unless (member op +store-index-opcodes+)
      (error 'bad-opcode :mnemonic op))
    (unless am
      (error 'bad-address-mode :mnemonic op :address-mode am))
    (let ((skel (get op 'opcode)))
      (unless skel (error "Missing OPCODE property on ~A" op))
      (cond 
	((eq am :ABSOLUTE)  skel)
	((eq am :ZERO-PAGE) (- skel 8))
	((or (and (eq op 'STX) (eq am :ZERO-PAGE-Y))
	     (and (eq op 'STY) (eq am :ZERO-PAGE-X)))
	 (+ skel 8))
	(t (error 'bad-address-mode :mnemonic op :address-mode am))))))

(defvar +load-index-opcodes+ '(LDX LDY))

(setf (get 'LDX 'opcode) 174)
(setf (get 'LDY 'opcode) 172)

(defun load-index-opcode-to-byte (symbolic-opcode)
  (let ((op (opcode symbolic-opcode))
	(am (address-mode symbolic-opcode)))
    (unless (member op +load-index-opcodes+)
      (error 'bad-opcode :mnemonic op))
    (unless am
      (error 'bad-address-mode :mnemonic op :address-mode am))
    (let ((skel (get op 'opcode)))
      (unless skel (error "Missing OPCODE property on ~A" op))
      (cond 
	((eq am :ABSOLUTE)   skel)
	((eq am :IMMEDIATE)  (- skel 12))
	((eq am :ZERO-PAGE)  (- skel 8))
	((or (and (eq op 'LDX) (eq am :ABSOLUTE-Y))
	     (and (eq op 'LDY) (eq am :ABSOLUTE-X)))
	 (+ skel 16))
	((or (and (eq op 'LDX) (eq am :ZERO-PAGE-Y))
	     (and (eq op 'LDY) (eq am :ZERO-PAGE-X)))
	 (+ skel 8))
	(t (error 'bad-address-mode :mnemonic op :address-mode am))))))

(defun opcode-to-byte (symbolic-opcode)
  (let ((op (opcode symbolic-opcode)))
    (cond 
      ((member op +branch-opcodes+)
       (branch-opcode-to-byte symbolic-opcode))
      ((member op +implied-opcodes+)
       (implied-opcode-to-byte symbolic-opcode))
      ((member op +accumulator-opcodes+)
       (accumulator-opcode-to-byte symbolic-opcode))
      ((member op +shift/rotate-opcodes+)
       (shift/rotate-opcode-to-byte symbolic-opcode))
      ((member op +inc/dec-opcodes+)
       (inc/dec-opcode-to-byte symbolic-opcode))
      ((member op +compare-index-opcodes+)
       (compare-index-opcode-to-byte symbolic-opcode))
      ((member op +load-index-opcodes+)
       (load-index-opcode-to-byte symbolic-opcode))
      ((member op +store-index-opcodes+)
       (store-index-opcode-to-byte symbolic-opcode))
      ((eq op 'BIT)
       (bit-opcode-to-byte symbolic-opcode))
      ((eq op 'JMP)
       (jmp-opcode-to-byte symbolic-opcode))
      ((eq op 'JSR)
       (jsr-opcode-to-byte symbolic-opcode))
      (t (error 'bad-opcode :mnemonic symbolic-opcode)))))