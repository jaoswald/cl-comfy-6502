;;; -*- mode: Lisp; Syntax: ANSI-Common-Lisp; Package: (COMFY-6502 ("6502" "CL")); -*-
;;;
;;; comfy-6502.lisp $Revision: 1.11 $
;;;
;;;
;;; LICENSE: This software is based on source code published by the 
;;; Association for Computing Machinery (ACM) in Sigplan Notices.
;;; Therefore it is subject to the ACM Software License Agreement.
;;; This grants to the user a royalty-free, nonexclusive right to 
;;; execute, copy, modify, and distribute both the binary and source
;;; code solely for academic, researce noncommercial
;;; uses.
;;;
;;; See ACM-LICENSE.txt for details.
;;;
;;; JAO: attempt to change to emit symbolic 6502 mnemonics so I can 
;;; read the generated code without a disassembler.
;;;
;;; Common Lisp version of COMFY-6502
;;; From http://home.pipeline.com/~hbaker1/sigplannotices/CFYCMP1.LSP
;;;
;;; See Henry G. Baker, `The COMFY 6502 Compiler,' 
;;      Garbage In, Garbage Out, Sigplan Notices, 
;;;     September 1997
;;; available in TeX format as 
;;; http://home.pipeline.com/~hbaker1/sigplannotices/column04.tex.gz
;;;
;;;

;;; todo: figure out what the (seq break return) in the example should
;;; do. Now, it ends up emitting a "nil RTS".
;;; a few Lisp utility functions

(cl:defpackage "COMFY-6502" 
  (:use "6502" "CL")
  (:shadow "COMPILE" "CONSTANTP" "VARIABLEP" "BREAK"
	   "IF" "+" "-" "1+" "1-" "NOT" "LOOP" ;; "PROG"
	   "FOR"
	   ;; "WHEN" "UNLESS" ; candidates for control macros
	   )
  (:export "COMPILE" "INIT" "*MEM*" "RELOCATE"
	   ;; "WHEN" "UNLESS"
	   "EQU"
	   "A" "S" "I@" "@J" "#" "I" "J"
	           "X@" "@Y"     "X" "Y"

	   "COMFY-6502-ERROR" "OPCODE-ERROR" "ADDRESS-MODE-ERROR"
	   "IF-ERROR" "PROBLEM" "ERROR-FORM" "ERROR-OPCODE" "ERROR-MODE"
	   "WHILE-ERROR"

	   "COMFY-MACROEXPAND" "DEFINE-CMACRO"

	   "SEQ" "ALT" "IF" "NOT" "WHILE" "LOOP"
	   "STAR" ;; "PROG"
	   "FORI" "FORJ" "MOVE"
	   "LISP"

	   "ST" "L" "C" "STJ" "LJ" "CJ" "STI" "LI" "CI" 
	   "+" "-" "1+" "1-"
	   "I+1" "I-1" "J+1" "J-1"
	   "LOR" "LAND" "LXOR"
	   "ASL" "RL" "LSR" "RR"
	   "?" "NOP"
	   "C=0" "C=1" 
	   "SEB" "CLB" "V=0" 
	   "=?" "~=?" 
	   "=0?" "ZERO?" "~=0?" 
	   "C=0?" "CARRY?" "C=1?" "LLT" "LGE" 
	   "V=0?" "V=1?" "<?" ">=?" "<0?" ">=0?"
	   "BINARY" "DECIMAL" "ENABLE" "DISABLE"
	   "TRAP" "BREAK" "SAVE" "RESTORE" 
	   "PUSH" "POP" 
	   "RETURN" "RESUME"))

(cl:in-package "COMFY-6502")

;;; Basic test instructions.
(setf (get 'c=1? 'test) 'BCS
      (get 'carry? 'test) 'BCS)    ;;; test carry=1. ; BCS
(setf (get 'c=0? 'test) 'BCC)    ;;; test carry=0. ; BCC
(setf (get 'llt 'test) 'BCC)      ;;; logically less than. ; BCC
(setf (get 'lge 'test) 'BCS)      ;;; logically greater than or equal. ; BCS
(setf (get '=? 'test) 'BEQ)      ;;; equal. ; BEQ
(setf (get '~=? 'test) 'BNE)     ;;; not equal. ; BNE
(setf (get '=0? 'test) 'BEQ
      (get 'zero? 'test) 'BEQ)     ;;; equals zero. ; BEQ
(setf (get '~=0? 'test) 'BNE)    ;;; not equal to zero. ; BNE
(setf (get 'v=1? 'test) 'BVS)    ;;; test overflow=1. ; BVS
(setf (get 'v=0? 'test) 'BVC)    ;;; test overflow=0. ; BVC
(setf (get '<? 'test) 'BMI)      ;;; test arithmetic less than. ; BMI
(setf (get '>=? 'test) 'BPL)     ;;; test arithmetic greater than or equal. ; BPL
(setf (get '<0? 'test) 'BMI)     ;;; test arithmetic less than zero. ; BMI
(setf (get '>=0? 'test) 'BPL)    ;;; test airthmetic greater than or equal to zero. ; BPL

;;; Group 0.
(setf (get '? 'skeleton) 'BIT
      (get 'BIT 'skeleton) 'BIT)  ;;; test.  
(setf (get 'stj 'skeleton) 'STY
      (get 'STY 'skeleton) 'STY)  ;;; store j, TYA
(setf (get 'TYA 'skeleton) 'TYA)

(setf (get 'lj 'skeleton) 'LDY
      (get 'LDY 'skeleton) 'LDY)  ;;; load j, TAY
(setf (get 'TAY 'skeleton) 'TAY)

(setf (get 'cj 'skeleton) 'CPY
      (get 'CPY 'skeleton) 'CPY)  ;;; compare j
(setf (get 'ci 'skeleton) 'CPX 
      (get 'CPX 'skeleton) 'CPX)  ;;; compare i.

;;; Group 1.
(setf (get 'lor 'skeleton) 'ORA
      (get 'ORA 'skeleton) 'ORA)  ;;; logical or.
(setf (get 'land 'skeleton) 'AND
      (get 'AND 'skeleton) 'AND)  ;;; logical and. 
(setf (get 'lxor 'skeleton) 'EOR
      (get 'EOR 'skeleton) 'EOR)  ;;; logical xor.
(setf (get '+ 'skeleton) 'ADC
      (get 'ADC 'skeleton) 'ADC)  ;;; add with carry.
(setf (get 'st 'skeleton) 'STA
      (get 'STA 'skeleton) 'STA)  ;;; store accumulator.
(setf (get 'l 'skeleton) 'LDA
      (get 'LDA 'skeleton) 'LDA)  ;;; load accumulator.
(setf (get 'c 'skeleton) 'CMP
      (get 'CMP 'skeleton) 'CMP)  ;;; compare accumulator.
(setf (get '- 'skeleton) 'SBC
      (get 'SBC 'skeleton) 'SBC)  ;;; subtract with borrow.

;;; Group 2.
(setf (get 'asl 'skeleton) 'ASL)  ;;; arithmetic shift left.
(setf (get 'rl 'skeleton)  'ROL
      (get 'ROL 'skeleton) 'ROL)  ;;; rotate left.
(setf (get 'lsr 'skeleton) 'LSR)  ;;; logical shift right.
(setf (get 'rr 'skeleton)  'ROR
      (get 'ROR 'skeleton) 'ROR)  ;;; rotate right.
(setf (get 'sti 'skeleton) 'STX
      (get 'STX 'skeleton) 'STX)  ;;; store i, TXA, TXS
(setf (get 'TXA 'skeleton) 'TXA)
(setf (get 'TXS 'skeleton) 'TXS)

(setf (get 'li 'skeleton) 'LDX
      (get 'LDX 'skeleton) 'LDX)  ;;; load i, TAX, TSX
(setf (get 'TAX 'skeleton) 'TAX)
(setf (get 'TSX 'skeleton) 'TSX)

(setf (get '1- 'skeleton) 'DEC
      (get 'DEC 'skeleton) 'DEC)  ;;; decrement. ;; DEC A not a 6502 opcode.
(setf (get '1+ 'skeleton) 'INC
      (get 'INC 'skeleton) 'INC)  ;;; increment.  ;; INC A not a 6502 opcode.

;;; random instructions.
(setf (get 'trap 'skeleton) 'BRK)  ;;; programmed break.
(setf (get 'save 'skeleton) 'PHP
      (get 'PHP 'skeleton) 'PHP)   ;;; push processor state onto stack
(setf (get 'restore 'skeleton) 'PLP
      (get 'PLP 'skeleton) 'PLP)   ;;; restore processor state from stack.
(setf (get 'push 'skeleton) 'PHA
      (get 'PHA 'skeleton) 'PHA)   ;;; push accumulator onto stack.
(setf (get 'pop 'skeleton) 'PLA
      (get 'PLA 'skeleton) 'PLA)   ;;; pop accumulator from stack.
(setf (get 'c=0 'skeleton) 'CLC
      (get 'CLC 'skeleton) 'CLC    ;;; clear carry.
      (get 'seb 'skeleton) 'CLC)   ;;; (== set borrow.)
(setf (get 'c=1 'skeleton) 'SEC    ;;; set carry. ; SEC
      (get 'SEC 'skeleton) 'SEC
      (get 'clb 'skeleton) 'SEC)   ;;; (== clear borrow.)

(setf (get 'v=0 'skeleton) 'CLV
      (get 'CLV 'skeleton) 'CLV)   ;;; clear overflow. ; CLV
(setf (get 'enable 'skeleton) 'CLI
      (get 'CLI 'skeleton) 'CLI)   ;;; enable interrupts.  ; CLI
(setf (get 'disable 'skeleton) 'SEI
      (get 'SEI 'skeleton) 'SEI)   ;;; disable interrupts. ; SEI
(setf (get 'binary 'skeleton) 'CLD
      (get 'CLD 'skeleton) 'CLD)   ;;; set binary mode. ; CLD
(setf (get 'decimal 'skeleton) 'SED
      (get 'SED 'skeleton) 'SED)   ;;; set decimal mode. ; SED

(setf (get 'i+1 'skeleton) 'INX
      (get 'INX 'skeleton) 'INX)     ;;; increment i. ; INX
(setf (get 'j+1 'skeleton) 'INY
      (get 'INY 'skeleton) 'INY)     ;;; increment j. ; INY
(setf (get 'i-1 'skeleton) 'DEX
      (get 'DEX 'skeleton) 'DEX)     ;;; decrement i. ; DEX
(setf (get 'j-1 'skeleton) 'DEY
      (get 'DEY 'skeleton) 'DEY)     ;;; decrement j. ; DEY

(setf (get 'nop 'skeleton) 'NOP)     ;;; no operation. ; NOP

(defvar jmp (6502:make-symbolic-opcode 'JMP :absolute)) ; JMP absolute
(defvar jsr (6502:make-symbolic-opcode 'JSR :absolute)) ; JSR absolute
(defvar break (6502:make-symbolic-opcode 'BRK :implied))

(setf (get 'return 'jump) (6502:make-symbolic-opcode 'RTS :implied))
(setf (get 'RTS 'jump) (get 'return 'jump)) ; RTS
(setf (get 'resume 'jump) (6502:make-symbolic-opcode 'RTI :implied)) ; RTI
(setf (get 'RTI 'jump) (get 'resume 'jump))

;; Condition types.

(defvar *current-form* nil "Form currently being compiled.")

(define-condition comfy-6502-error (error)
  ((error-form :reader error-form :initarg :error-form
	       :initform *current-form*))
  (:report (lambda (condition stream)
	     (format stream "COMFY-6502-ERROR compiling form ~A"
		     (error-form condition)))))

(define-condition opcode-error (comfy-6502-error)
  ((error-opcode :reader error-opcode :initarg :error-opcode)
   (problem :reader problem :initarg :problem))
  (:report (lambda (condition stream)
	     (format stream "COMFY-6502 Opcode ~A ~A in form ~A"
		     (error-opcode condition)
		     (problem condition)
		     (error-form condition)))))

(define-condition address-mode-error (comfy-6502-error)
  ((error-mode :reader error-mode :initarg :error-mode)
   (problem :reader problem :initarg :problem))
  (:report (lambda (condition stream)
	     (format stream "COMFY-6502 Address mode ~A ~A in form ~A"
		     (error-opcode condition)
		     (problem condition)
		     (error-form condition)))))

;; opcode manipulations

(defun inv (c)
  ;;; invert the condition for a branch.
  ;;; invert bit 5 (counting from the right).
  (cond
   ((eql c 'BCS) 'BCC)
   ((eql c 'BCC) 'BCS)
   ((eql c 'BEQ) 'BNE)
   ((eql c 'BNE) 'BEQ)
   ((eql c 'BVS) 'BVC)
   ((eql c 'BVC) 'BVS)   
   ((eql c 'BMI) 'BPL)
   ((eql c 'BPL) 'BMI)
   (t (error 'opcode-error :error-opcode c
	     :problem "is not a branch"))))

(defun skeleton (op)
  (let ((skel (get op 'skeleton)))
    (cl:unless skel
      (error 'opcode-error :error-opcode op
	     :problem "not an implied opcode"))
    skel))

;; Accumulator opcode includes a few "puns" from Baker's original
;; (li a) is TAX, (lj a) is TAY
;; (sti a) is TXA, (stj a) is TYA
;; ASL A, LSR A, ROL A, ROR A are the only others in basic
;; 6502

(defun accumulator-op (op)
  (let ((skel (skeleton op)))
    (cond ((eq skel 'LDX) (make-symbolic-opcode 'TAX :implied))
	  ((eq skel 'LDY) (make-symbolic-opcode 'TAY :implied))
	  ((eq skel 'STX) (make-symbolic-opcode 'TXA :implied))
	  ((eq skel 'STY) (make-symbolic-opcode 'TYA :implied))
	  ((member skel 6502::+shift/rotate-opcodes+)
	   (make-symbolic-opcode (skeleton op) :ACCUMULATOR))
	  (t (error 'opcode-error :error-opcode op
		    :problem "does not support ACCUMULATOR mode")))))

(defun stack-op (op)
  (let ((skel (skeleton op)))
    (cond ((eq skel 'LDX) (make-symbolic-opcode 'TSX :implied))
	  ((eq skel 'STX) (make-symbolic-opcode 'TXS :implied))
	  (t (error 'opcode-error :error-opcode op
		    :problem "does not support STACK mode")))))

;; implied includes also opcodes which can default to "A"
;; mode if no operand is given.
;; ASL A, LSR A, ROL A, ROR A are the only ones in basic 6502

(defun implied-op (op)
  (let ((skel (skeleton op)))
    (cond
      ((member skel 6502::+implied-opcodes+) 
       (make-symbolic-opcode skel :IMPLIED))
      ((member skel 6502::+shift/rotate-opcodes+)
       (make-symbolic-opcode skel :ACCUMULATOR))
      (t (error 'opcode-error :error-opcode op
		:problem "does not support IMPLIED mode")))))

;; immediate (8-bit constant) operations
(defun immediate-op (op)
  (make-symbolic-opcode (skeleton op) :IMMEDIATE))

(defun absolute-op (op)
  (make-symbolic-opcode (skeleton op) :ABSOLUTE))

(defun abs-to-zp-marker (marker)
  (cond 
   ((eq marker :ABSOLUTE-X) :ZERO-PAGE-X)
   ((eq marker :ABSOLUTE) :ZERO-PAGE)
   (T (error 'address-mode-error 
	     :error-mode marker
	     :problem " has no zero page equivalent"))))

(defmethod abs-to-zp ((op 6502:symbolic-opcode))
  (make-symbolic-opcode (opcode op) (abs-to-zp-marker (address-mode op))))

(defun zp-op (op)
  (make-symbolic-opcode (skeleton op) :ZERO-PAGE))

(defun x-indirect-op (op)
  (make-symbolic-opcode (skeleton op) :ZP-X-INDIRECT))

(defun indirect-y-op (op)
  (make-symbolic-opcode (skeleton op) :ZP-INDIRECT-Y))		;

(defun absolute-x (op)
  (make-symbolic-opcode (skeleton op) :ABSOLUTE-X))

(defun absolute-y (op)
  (make-symbolic-opcode (skeleton op) :ABSOLUTE-Y))

;;; process opcode symbols/macro symbols

(defun testp (e)
  ;;; predicate to tell whether "e" is a test.
  (and (symbolp e) (get e 'test)))

(defun actionp (e)
  ;;; predicate to tell whether "e" is an action.
  (and (symbolp e) (cl:not (get e 'test))))

(defun jumpp (e)
  ;;; predicate to tell whether "e" is a jump-type action.
  (and (symbolp e) (get e 'jump)))

(defun macrop (x)
  (and (symbolp x) (get x 'cmacro)))

(defvar *mem* nil
  "List where the compiled code is placed. 
Contains elements of the following types: symbolic opcodes, 
constant numbers (which must fit in one byte),  or lists 
of the following forms

  (:BYTE <expr>) : a one-byte number

  (:BRANCH <number>) : a one-byte branch, with the destination relative
                       to the BRANCH byte (off-by-one from 6502 branch value)

  (:LONG-BRANCH <number>) : a two-byte branch, destination relative to the
                            first of the two LONG-BRANCH bytes (6502 absolute
                            jump will be calculated during relocation)

  (:ZERO-PAGE <expr>) : a zero-page address reference. 

  (:ABSOLUTE <expr>) : a two-byte address reference.")

(defvar *f* 0
  "Compiled code length counter. It reflects how many bytes of code have been
emitted into the list.")

(defvar *symbol-table* (make-hash-table))

(defun init ()
  (setf *mem* nil)
  (setq *f* 0))

(init)

(defun mem-length (obj)
  "Given an object that can be in the emitted code list, returns the
size of the object in bytes."
  (cond ((numberp obj)
	 (cl:if (<= -128 obj 255)
		1
		(error "Exceeds byte range")))
	((eq (class-of obj) (find-class '6502:symbolic-opcode))
	 1)
	((consp obj)
	 (cond ((or (eq (car obj) :BRANCH)
		    (eq (car obj) :ZERO-PAGE)
		    (eq (car obj) :BYTE))
		1)
	       ((or (eq (car obj) :LONG-BRANCH)
		    (eq (car obj) :ABSOLUTE)
		    (eq (car obj) :WORD))
		2)))
	(t (error "Unknown object."))))

(defun relocate (code-vector org-address)
  "Convert a list of compiled elements into a list of byte values,
by resolving branch and address references. ORG-ADDRESS is the 
absolute address of the first element of the list. All addresses
must be in numeric form."
  (let ((addr org-address)
	(linked nil))
    (labels ((relocate-branch (br)
	       (cl:unless (<= -127 (second br) 128)
		 (error "Illegal short branch"))
	       (cl:push (cl:+ (second br) 1) linked)
	       (incf addr))
	     (relocate-long-branch (br)
	       (let ((abs (cl:+ (second br) addr)))
		 (cl:push (ldb (byte 8 0) abs) linked)
		 (cl:push (ldb (byte 8 8) abs) linked)
		 (incf addr 2)))
	     (relocate-zp (zp)
	       (cl:push (ldb (byte 8 0) (second zp)) linked)
	       (incf addr))
	     (relocate-abs (abs)
	       (cl:push (ldb (byte 8 0) (second abs)) linked)
	       (cl:push (ldb (byte 8 8) (second abs)) linked)
	       (incf addr 2)))
      (dolist (obj code-vector (nreverse linked))
	(cond ((numberp obj) (cl:push obj linked) (incf addr))
	      ((eq (class-of obj) (find-class '6502:symbolic-opcode))
	       (cl:push obj linked) 
	       (incf addr))
	      ((consp obj) 
	       (case (car obj)
		 (:BYTE        (cl:push (second obj) linked))
		 (:BRANCH      (relocate-branch obj))
		 (:LONG-BRANCH (relocate-long-branch obj))
		 (:ZERO-PAGE   (relocate-zp obj))
		 (:ABSOLUTE    (relocate-abs obj))))
	      (t (error "Don't know how to relocate ~S" obj)))))))


(defun memref (f)
  "Convert an integer memory position F into the portion of the
*MEM* list beginning at that point. *F* contains the total byte count.
F is measured relative to the first emitted byte, i.e. the last byte
in the list.

F = 0 refers to the last element of the list, F = *F* the first."
  (cl:if (> f *f*)
	 (error "Reference to non-existent location.")
	 (do ((distance (cl:- *f* f) distance)
	      (ptr *mem* (cdr ptr)))
	     ((<= distance 0) ptr)
	   (decf distance (mem-length (car ptr))))))

(defun gen (obj)
  ;;; place one character "obj" into the stream.
  (incf *f*)
  (cl:push obj *mem*)
  *f*)


(defun update-long-branch (location addr)
  "Replace the long-branch address argumnet of the instruction 
located at offset LOCATION with the (relative) address ADDR. 
LOCATION is the offset of the JMP/JSR instruction itself."
  (let* ((ptr (memref location))
	 (inst (car ptr))
	 (branch (second ptr)))
    (cl:unless (and (eq (class-of inst) (find-class '6502:symbolic-opcode))
		 (equal (car branch) :LONG-BRANCH))
      (error "update-long-branch: not an long branch address"))
    (setf (second branch) (cl:- location addr 1))
    location))


(defun genbr (win)
  ;;; generate an unconditional jump to "win".
  ;;; (genbr NIL) creates a unconditional jump with a NIL destination.
  ;;;
  ;;; JMP (:LONG-BRANCH dist) [current *f*] ...
  ;;; dist = 2 branches to current *f*; win below f increases distance
  (let ((distance (cl:if (null win)
			 nil
			 (cl:+ 2 (cl:- *f* win)))))
    (cl:push (list :LONG-BRANCH distance) *mem*)
    (incf *f* 2)
    (gen jmp)
    *f*))

(defun 8bitp (n)
  (let* ((m (logand n -128)))
    (or (= 0 m) (= -128 m))))

(defun genbrc (c win lose)
  ;;; generate an optimized conditional branch
  ;;; on condition c to "win" with failure to "lose".
  ;;; JAO: what is the definition of the return value?
  ;;; JAO: the address to "enter" the branch
  ;;; JAO: note, that if win=lose this will return win without generating
  ;;; code.
  ;;; JAO...dependent on branch range as well as length of instructions
  ;;;
  ;;; win/lose are relative to location past end of *mem* = 0
  ;;; win/lose = *f* are to location at beginning of *mem*
  (let* ((w (cl:- *f* win)) 
	 (l (cl:- *f* lose))) ;;; Normalize to current point.
    (labels ((gen-instruction (cond)
	       (gen (6502:make-symbolic-opcode cond :branch-relative)))
	     (gen-branch (loc)
	       (gen (list :BRANCH loc))))
    (cond 
      ;; win and lose equivalent
      ;; ((= w l) (print "case 1") win) 
      ;; ... no test needed and no instructions to emit
      ((and (= l 0) (= w 0)) win)
      ;; win and lose equivalent, but do we need to emit a branch there?
      ;; three byte absolute jump always shorter than Bwin w+2 Blose l
      ;; but an 8-bit BRA (as in 65c02) would allow a one-byte savings
      ;; here for w,l within 8 bit branch
      ;; ...the BRA change could also go in genbr...
      ((= w l) win) ;; (genbr win))
      
      ;; JAO: lose is falling through, w is a short branch
      ;; note, 6502 branch values are a "delta" of the PC from the 
      ;; ordinary PC=next-instruction
      ;; B<win-condition> (:BRANCH w) ...losing instructions...
      ((and (= l 0) (8bitp w)) 
       (gen-branch (cl:1+ w))
       (gen-instruction c))
      
      ;; win is falling through, l is a short branch
      ;; B<lose-condition> (:BRANCH l) ...winning instructions...
      ((and (= w 0) (8bitp l)) 
       (gen-branch (cl:1+ l)) 
       (gen-instruction (inv c)))
	
      ;; note in this case, w+2 because we must reach
      ;; w relative to freshly emitted two-byte branch
      ;; B<win-condition> w+2 B<lose-condition> l [l or w bytes skipped] ...
      ((and (8bitp l) (8bitp (cl:+ w 2))) 
       (gen-branch (cl:1+ l)) 
       (gen-instruction (inv c))
       (gen-branch (cl:+ w 3)) 
       (gen-instruction c))

      ;; rare case when switching win & lose is just enough to reach w
      ;; with a short branch.
      ;; B<lose-condition> l+2 B<win-condition> w [l or w bytes skipped]
      ;; case 6
      ((and (8bitp w) (8bitp (cl:+ l 2))) 
       (gen-branch (cl:1+ w)) 
       (gen-instruction c) 
       (gen-branch (cl:+ l 3)) 
       (gen-instruction (inv c)))
      
      ;; JAO: lose can be reached through short branch, win is long
      ;; result will be 
      ;; B<lose-condition> <l+3> JMP win-lo win-high <l bytes skipped>
      ;;                                             ...losing instructions...
      ;; generated by moving win to front of instruction stream 
      ;; and using the win-is-falling-through, l is short branch case
      ;; treated above
      ;; case 7: long branch to win, recurse through case 4
      ((8bitp (cl:+ l 3)) 
       (genbrc c (genbr win) lose))
      
      ;; case 8: long branch to lose, recurse through case 7
      ;; default: B<lose-condition> 3 JMP win-lo win-hi JMP lose-lo lose-hi
      ;; but generated by moving lose to front of instruction stream
      ;; and using lose-is-short-branch, win long branch (previous clause)
      (t (genbrc c win (genbr lose)))))))

(defun one-byte-gen (op-code a)
  ;;; put op code and one-byte argument into stream.
  ;;; op-code should be the correct addressing mode
  (let* ((la (cl:if (numberp a)
		    (logand a 255)
		    a)))
    (gen la) 
    (gen op-code)))

  
(defun zero-page-ref (value original-form)
  "Return (:ZERO-PAGE ...) if value is a valid zero-page address, 
or something symbolic and asserted to be zero-page by the user. 
NIL if value not guaranteed or asserted to be zero-page"
  (cond 
    ((numberp value) 
     (cl:if (<= 0 value 255)
	    (list :ZERO-PAGE value)
	    nil))
    ((symbolp value) 
     (cl:when (eq value :ZERO-PAGE)
       (list :ZERO-PAGE original-form)))
    ((consp value) 
     (cl:when (eq (car value) :ZERO-PAGE)
       value))
    (t nil)))

(defun absolute-ref (value original-form)
  "Return (:ABSOLUTE ...) if value is a valid address, 
or something symbolic."
  (cond 
    ((numberp value) 
     (cl:if (<= -32768 value 65535)
	    (list :ABSOLUTE value)
	    (error "Exceeds address range.")))
    ((symbolp value) 
     (cl:when (or (eq value :ABSOLUTE) (eq value :ZERO-PAGE))
       (list :ABSOLUTE original-form)))
    ((consp value) 
     (cl:when (or (eq (car value) :ZERO-PAGE)
		  (eq (car value) :ABSOLUTE))
       value))
    (t nil)))

(defun ogen (op-code a)
  ;;; put out address and op code into stream.
  ;;; compact to one byte zero page address, if possible.
  ;;; op-code should be the absolute addressing mode.
  (let* ((argval (eval-address-expression a *symbol-table*))
	 (zp (zero-page-ref argval a)))
    (cl:if zp
	   (one-byte-gen (abs-to-zp op-code) zp)
	   (let ((abs (absolute-ref argval a)))
	     (cl:if abs
		    (gen-absolute op-code abs)
		    (error "Invalid address argument ~A" a))))))

(defun gen-zero-page (opcode arg)
  (gen (eval-zp-expression arg *symbol-table*))
  (gen opcode))

(defun gen-absolute (opcode arg)
  (cl:push (eval-absolute-expression arg *symbol-table*) *mem*)
  (incf *f* 2)
  (gen opcode))

(defun emit-byte (arg)
  (gen (list :BYTE (eval-immediate-expression arg *symbol-table*))))


(defun emit (i win)
  (let ((*current-form* i))
  ;;; place the unconditional instruction "i" into the stream with
  ;;; success continuation "win".
    (cond ((cl:not (= win *f*)) (emit i (genbr win)))

        ;;; atom is a single character instruction.
	  ((symbolp i) (gen (implied-op i)))
	  
        ;;; no op code indicates a subroutine call.
	  ((null (cdr i)) (gen-absolute jsr (car i)))
	  
        ;;; "a" indicates the accumulator.
	  ((eq (cadr i) 'a) (gen (accumulator-op (car i))))
	  
        ;;; "s" indicates the stack.
	  ((eq (cadr i) 's) (gen (stack-op (car i))))
	  
        ;;; length=2 indicates absolute addressing.
        ;;; might reduce to zero-page
	  ((= (length i) 2)
	   (ogen (absolute-op (car i)) (cadr i)))
	  
        ;;; "i" indicates absolute indexed by i.
        ;;; could be absolute-x or zero-page-x
	  ((or (eq (cadr i) 'i)
	       (eq (cadr i) 'x))
	   (ogen (absolute-x (car i)) (caddr i)))
	  
        ;;; "j" indicates absolute indexed by j.
        ;;; this cannot be optimized for page zero addresses.
	  ((or (eq (cadr i) 'j) 
	       (eq (cadr i) 'Y))
	   (gen-absolute (absolute-y (car i))
			 (caddr i)))
	  
        ;;; "\#" indicates immediate operand.
        ;;; one-byte immediates only
	  ((eq (cadr i) '\#)
	   (emit-byte (caddr i)) (gen (immediate-op (car i))))
	  
        ;;; "i@" indicates index by i, then indirect.
        ;;; zero-page only
	  ((or (eq (cadr i) 'i@) 
	       (eq (cadr i) 'x@))
	   (gen-zero-page 
	    (x-indirect-op (car i)) 
	    (caddr i)))
	  
        ;;; "@j" indicates indirect, then index by j.
        ;;; zero-page only
	  ((or (eq (cadr i) '@j) 
	       (eq (cadr i) '@y))
	   (gen-zero-page 
	    (indirect-y-op (car i))
	    (caddr i)))
	  
	  (t (error 'comfy-6502-error)))))


;;; compile routines emit the relevant code; the return
;;; value is the address of the continuation produced.
;;; compilation emits the code starting at the last instruction.

;;; A;B;C;... 
;;; each element is executed in sequence, with a common "lose"
;;; and the next element as the "win"
(defun compile-seq (seq-list win lose)
  (cl:if (null seq-list)
	 win
	 (compile (car seq-list)
		  (compile-seq (cdr seq-list) win lose)
		  lose)))

;;; (<number> <form>) with win/lose
;;; 
(defun compile-repeat (number form win lose)
  (cl:if (zerop number) 
	 win
	 (compile-repeat (cl:1- number) form 
			 (compile form win lose)
			 lose)))

;;; if test-form win-test-form lose-test-form
;;; the resulting continuation executes the test-form.
;;; if that test succeeds, the win-test-form is executed (winning or losing)
;;;         test fails, the lose-test-form is executed (winning or losing)

(define-condition if-error (comfy-6502-error)
  ((problem :reader problem :initarg :problem))
  (:report (lambda (condition stream)
	     (format stream "COMFY-6502 ERROR compiling IF form ~A ~A"
		     (error-form condition)
		     (problem condition)))))
	     

(defun compile-if (test-form win-form lose-form win lose)
  (cl:when (null win-form)
    (error 'if-error :problem "lacking win-form"))
  (cl:when (null lose-form)
    (error 'if-error :problem "lacking lose-form"))
  (let ((win-test (compile win-form win lose))
	(lose-test (compile lose-form win lose)))
    (compile test-form win-test lose-test)))

;;;; while test-form body-form
;;; execute test-form
;;;    if the test wins, execute body-form
;;;       if body-form wins, loop through again
;;;       if body-form loses, the whole while loses
;;;    if the test loses, the body-form is not executed, but the
;;;       whole while form wins.

(define-condition while-error (comfy-6502-error)
  ((problem :reader problem :initarg :problem))
  (:report (lambda (condition stream)
	     (format stream "COMFY-6502 ERROR compiling WHILE form ~A ~A"
		     (error-form condition)
		     (problem condition)))))             

(defun compile-while (test-form win-form win lose)
  (cl:when (null test-form)
    (error 'while-error :problem "lacking test-form"))
  (cl:when (null win-form)
    (error 'while-error :problem "lacking win-form"))
  (let* ((jump-begin (genbr nil)) ; will fill with branch back to test-form
	 (while-entry 
	  (compile test-form
		   (compile win-form jump-begin lose) 
		   win)))
    (update-long-branch jump-begin while-entry)
    while-entry))

(define-condition loop-error (comfy-6502-error)
  ((problem :reader problem :initarg :problem))
  (:report (lambda (condition stream)
	     (format stream "COMFY-6502 ERROR compiling LOOP form ~A ~A"
		     (error-form condition)
		     (problem condition)))))

(defvar *optimize-loop-branches* T "Enables optimization of loop branches")
 
(defun optimize-loop (bottom-jump)
  "Attempt to optimize LOOP body; branch shorten conditional branches
to the BOTTOM-JUMP location, attempt to remove BOTTOM-JUMP or replace
it with a conditional backward branch.

   FOR NOW: only shorten conditional branches."

  (let* ((backward-jump (memref bottom-jump))
	 (backward-branch (cadr backward-jump)))
    (unless (and (eq (class-of (car backward-jump))
		     (find-class 'symbolic-opcode))
		 (eq (opcode (car backward-jump)) '6502:JMP)
		 (eq (address-mode (car backward-jump)) :ABSOLUTE))
      (error 'loop-error :problem "bad bottom jump"))
    (unless (and (consp backward-branch)
		 (eq (car backward-branch) :LONG-BRANCH)
		 (numberp (cadr backward-branch)))
      (error 'loop-error :problem "bad bottom branch"))
    (let ((jump-length (cadr backward-branch)))
      ;;
;;      (format t "optimizing loop: bottom-jump ~D ~
;;                 backward-branch ~A jump-length ~D~%"
;;	      bottom-jump backward-branch jump-length)

      (do ((code-ptr *mem* (cdr code-ptr))
	   (obj-addr *f* (cl:- obj-addr (mem-length (car code-ptr)))))
	  ((eq code-ptr backward-jump) *mem*)
	(let ((code-obj (car code-ptr)))
	  (when (and *optimize-loop-branches* 
		     (consp code-obj)
		     (eq (car code-obj) :BRANCH)
		     (numberp (cadr code-obj))
		     ;; (not (format t "Branch length ~D obj-addr ~D~%"
		     ;;	             (cadr code-obj) obj-addr))
		     (= (cl:- obj-addr (cadr code-obj)) bottom-jump)
		     ;;(not (format t "Branches to absolute jump~%"))
		     )
	    (let ((net-length (cl:+ 1 (cadr code-obj) jump-length)))
	      (when (<= -127 net-length 128)
		(setf (cadr code-obj) net-length)))))))))

;;; (loop loop-form)
;;; executes LOOP-FORM repeatedly. If LOOP-FORM ever fails, the 
;;; loop fails. 
;;;
;;; EXTENSION: "implied seq"
;;; (loop [forms]*) equivalent to (loop (seq [forms]*))

(defun compile-loop (loop-rest win lose)
  (declare (ignore win)) ; LOOP can never win
  ;(unless (null (cdr loop-rest))
  ;  (error "COMFY-6502:LOOP accepts only one form."))
  (let* ((l (genbr nil))
	 (r (compile-seq loop-rest l lose)))
    (update-long-branch l r)
    (optimize-loop l)
    r))
    
;;; IF, WHILE, LOOP, NOT, SEQ, <number>
(defun compile (e win lose)
  ;;; compile expression e with success continuation "win" and
  ;;; failure continuation "lose".
  ;;; "win" an "lose" are both addresses of stuff higher in memory.
  (let ((*current-form* e))
    (cond ((numberp e) (gen e))           ; allow constants.
	  ((macrop e) ; symbol macros
	   (compile (comfy-macroexpand e) win lose))
	  ((jumpp e) (gen (get e 'jump))) ; must be return or resume.
	  ((actionp e) (emit e win))      ; single byte instruction.
	  ((testp e) (genbrc (get e 'test) win lose)) ; test instruction
	  ((eq (car e) 'comfy-6502:not) (compile (cadr e) lose win))
	  ((eq (car e) 'seq) (compile-seq (cdr e) win lose))
	  ((eq (car e) 'comfy-6502:loop) (compile-loop (cdr e) win lose))
	  ((numberp (car e))              ; duplicate n times.
	   (compile-repeat (car e) (cadr e) win lose))
	  ((eq (car e) 'if)               ; if-then-else.
	   (cl:unless (null (cddddr e))
	     (error 'if-error :problem "too many forms"))
	   (compile-if (cadr e)
		       (caddr e) (cadddr e)
		       win lose))
	  ((eq (car e) 'while)            ; do-while.
	   (cl:unless (null (cdddr e))
	     (error 'while-error :problem "too many forms"))
	   (compile-while (cadr e) (caddr e) win lose))
	  ((macrop (car e))
	   (compile (comfy-macroexpand e) win lose))
	  (t (emit e win)))))

;;; a pattern-matching macro definer, following Baker's COMFY macros
;;; interpretively matching patterns
;;; variables are indicated by symbols beginning with the character #\?
;;; e.g ?x, ?VAR, etc.

;;; FIXME: grossly inefficient pattern matcher. Grossness is centered in
;;; apply-expander-or-fail, which compiles a function *every time
;;; the COMFY macro is expanded.*

;;; probably don't need to eval-when these cmacro building functions
;;; to ensure defn before the (define-cmacro 
;;; forms are executed. define-cmacro only has to 
;;; affect the symbol plists in time for (comfy-6502:compile ...)


(defun match-variable-p (thing)
  (and (symbolp thing) (char= (char (symbol-name thing) 0) #\?)))

(defun match-predicate (x)
  (and (consp x) (eq (car x) :in)))

(defun match-or-fail (p e f alist)
  ;;; f is a function which is executed if the match fails.
  ;;; f had better not return.
  ;;; JAO: otherwise, returns an ALIST mapping variable names to 
  ;;;      what they matched
  
  (cond  
    ;; variables match anything, and create/override an association
    ((match-variable-p p) (cons (cons p e) alist))
    ;; note: unlike Baker, variables are atoms, not conses, so they
    ;; have to be checked first
    
    ((atom p)
     (cond ((eq p e) alist)  ; constants match themselves
	   (t (funcall f)))) ; or fail
    
    
    ;; quoted elements in the pattern must be EQ to the expression
    ((eq (car p) 'quote) (cond ((eq (cadr p) e) alist)
			       (t (funcall f))))
    
    ;; predicates are called on the expression, return value T
    ;; indicates match
    ;; (:in <function>) tests against predicate <function>
    ;; (:in <function> <var>) collects a binding of <var> to the value
    ((match-predicate p) (cond ((funcall (cadr p) e) 
				(cl:if (endp (cddr p))
				       alist
				       (cons (cons (caddr p) e) alist)))
			       (t (funcall f))))
    
    ;; an atom not matched by now: failure
    ((atom e) (funcall f))
    
    ;; expression is a CONS: match recursively.
    (t (match-or-fail (car p)
		      (car e)
		      f
		      (match-or-fail (cdr p)
				     (cdr e)
				     f
				     alist)))))

;;; JAO: following works, but is quite crude:
;;; it compiles/conses up a function every time it is expanded.
;;; the trick is to reliably extract the order in which the 
;;; match will cons up the alist...
;;; is it as simple as finding the "alist cons" in the matcher
;;; and using it to update the "interpreter/compiler form" of the match?


(defun apply-expander-or-fail (pattern expression expansion fail)
  (multiple-value-bind (matched alist)
      (match pattern expression)
    (cl:if matched
	(let ((expander (cons 'lambda (cons (mapcar #'car alist)
					    expansion))))
	  (format t "expander ~A~%" expander)
	  ;; could also be (apply (compile nil expander) ...
	  (apply (coerce expander 'function)
		 (mapcar #'cdr alist)))
	(funcall fail))))


(defun match (p e)
  "Returns two values: first is T if match succeeded, NIL if match failed.
   Second is the alist of variables to their matches."
  (let ((success nil)
	(alist nil))
    (catch 'match-failed 
      (setq alist
	    (match-or-fail p e #'(lambda () (throw 'match-failed nil)) alist)
	    success T))
    (values success alist)))

(defmacro define-cmacro (name &rest expansions)
  "(define-cmacro name
      (pattern-form-1 &body expansion-1)
      (pattern-form-2 &body expansion-2)
      ....)"
  ;; FIXME: is this the right time to expand..?
  ;; or should I just be returning a symbol.
  `(progn
    (cl:when (get ',name 'cmacro)
      (warn "Redefining cmacro ~S" ',name))
    (setf (get ',name 'cmacro)
     #'(lambda (form)
	 (do ((exp ',expansions (cdr exp)))
	     ((null exp) (error "No pattern mached for form ~S" form))
	   (multiple-value-bind (matched alist)
	       (match (caar exp) form)
	     (cl:when matched
	       (let ((expander (cons 'lambda (cons (mapcar #'car alist)
						   (cdar exp)))))
		 ;; (format t "expander ~A~%" expander)
		 ;; could also be (apply (compile nil expander) ...
		 (cl:return (apply (coerce expander 'function) 
				   (mapcar #'cdr alist)))))))))
    ',name))

(defun comfy-macroexpand (form)
  (cl:if (consp form)
	 (let ((expander (get (car form) 'cmacro)))
	   (cl:unless expander
	     (error "No cmacro defined for ~S" (car form)))
	   (funcall expander form))
	 (let ((expander (get form 'cmacro)))
	   (cl:unless expander
	     (error "No cmacro defined for ~S" form))
	   (funcall expander form))))

#||
(setf (get 'alt 'cmacro)
      #'(lambda (e)
    ;;; define the dual of "seq" using DeMorgan's law.
	(list 'not
	      (cons 'seq
		    (mapcar #'(lambda (e) (list 'not e))
			    (cdr e))))))

||#

(define-cmacro alt
  ((alt . ?body)
   (list 'comfy-6502:not
	 (cons 'comfy-6502:seq
	       (mapcar #'(lambda (e) (list 'comfy-6502:not e))
		       ?body)))))

(define-cmacro star
  ((star . ?body)
   `(not (loop (seq ,@?body)))))

(define-cmacro rr-example
  ((rr-example) '(rl 8))
  ((rr-example ?place) `(rl 8 ,?place)))

;;; DON'T KNOW HOW TO MAKE THIS WORK unless literal number 
;;; is passed in...
;;; FIXME

;;; increment a 16-bit variable
;;; requires ability to do math on the address of the variable
(define-cmacro i2
  ((i2 ?p) `(seq (1+ ,?p) (if =0? (1+ (1+ ,?p)) (seq)))))

;;; JAO: these seem to be matching somewhat differently than
;;; Baker's
(define-cmacro move

;;  ((move (?x) (?y)) 
;;   (format t "match 2: ?x ~S ?y ~S" ?x ?y)
;;   `(seq (l ,?x) (st ,?y))))

  ((move ?x ?y) 
   (format t "match 1: ?x ~S ?y ~S" ?x ?y)
   `(seq ,(append (list 'l) ?x)
     ,(append (list 'st) ?y))))

#||
(define-cmacro comfy-6502:prog 
  ((prog ?v . ?body)
  `(seq push
    (li s)
    (move ,?v (i 257))
    ,(append '(seq) ?body)
    (li s)
    (move (i 257) ,?v)
    i-1
    (sti s))))
||#

(define-cmacro fori
  ((fori ?from ?to . ?body)
   `(seq ,(append '(li) ?from)
     (while (seq ,(append '(ci) ?to) llt)
       (seq ,(append '(seq) ?body) i+1)))))

(define-cmacro forj
  ((forj ?from ?to . ?body)
  `(seq ,(append '(lj) ?from)
    (while (seq ,(append '(cj) ?to) llt)
      (seq ,(append '(seq) ?body) j+1)))))

(define-cmacro for
  ((for ?v ?from ?to . ?body)
   `(seq ,(append '(l) ?from) ,(append '(st) ?v)
     (while (seq ,(append '(c) ?to) llt)
       (seq ,(append '(seq) ?body)
	    ,(append '(1+) ?v)
	    ,(append '(l) ?v))))))
#||
(setf (get 'call 'cmacro)
      #'(lambda (e)
	  (let* ((p (cadr e)) (pl (cddr e)))
	    (sublis (list (cons 'pushes (genpush pl))
			  (cons 'p p)
			  (cons 'n (length pl)))
		    '(seq (seq . pushes)
                    (p)
                    (li s)
                    (land ii)
                    (sti s))))))

(setf (get
 'lambda
 'cmacro)
 (lambda (e)
    (let* ((pl (cadr e))
           (body (cddr e)))
      (sublis (list (cons 'body body)
                    (cons 'xchs (genxchs pl))
                    (cons 'moves (genmoves pl)))
              '(seq (li s)
                    (seq . xchs)
                    (seq . body)
                    (li s)
                    (seq . moves)
                    (return))))))

(defun genxchs (pl)
  (cond ((null pl) pl)
        (t (cons (list 'xch (list 'i (+ 258 (length pl))) (list (car pl)))
                 (genxchs (cdr pl))))))

(defun genmoves (pl)
  (cond ((null pl) nil)
        (t (cons (list 'move (list 'i (+ 258 (length pl))) (list (car pl)))
                 (genmoves (cdr pl))))))

(defun genpush (pl)
  (cond ((null pl) pl)
        (t (let* ((p (car pl)))
             (append `((l ,p) push)) (genpush (cdr pl))))))


(defun match (p e f alist)
  ;;; f is a function which is executed if the match fails.
  ;;; f had better not return.
  ;;; JAO: otherwise, returns an ALIST mapping variable names to 
  ;;;      what they matched
  
  (cond ((constantp p)
         (cond ((eq p e) alist)  ; constants match themselves
               (t (funcall f)))) ; or fail

;; variables match anything, and create/override an association
        ((variablep p) (cons (cons (cadr p) e) alist)) 

;; quoted elements in the pattern must be EQ to the expression
        ((eq (car p) 'quote) (cond ((eq (cadr p) e) alist)
                                   (t (funcall f))))

;; predicates are called on the expression, return value T
;; indicates match
        ((predicate p) (cond ((funcall (cadr p) e) alist)
                             (t (funcall f))))

;; an atom not matched by now: failure
        ((atom e) (funcall f))

;; expression is a CONS: match recursively.
        (t (match (car p)
                  (car e)
                  f
                  (match (cdr p)
                         (cdr e)
                         f
                         alist)))))


;;; JAO: need to alter these to fit a CL 
;;; syntax for comma: probably should not have 
;;; edited all these forms without distinguishing
;;; between commas inside (` ) forms and those
;;; in the define cmacro stuff

(defun predicate (x)
  (and (consp x) (eq (car x) 'in)))

(defun constantp (x) (atom x))

(defun variablep (x)
  ;;(and (symbolp x) (char= #\? (char (symbol-name x) 0))))
  (and (consp x) (eq (car x) '?)))

(defun constantp (x) (atom x))

(defmacro cases (&rest a)
  `(quote
      ,(catch 'cases
           (fapplyl (cdr a)
                    (eval (car a))
                    (lambda () (throw 'cases nil))))))

(defun fapplyl (fl a fail)
  ;;; "fail" is a function which is executed if fapplyl fails.
  ;;; "fail" had better not return.
  (cond ((null fl) (funcall fail))
        (t (catch 'fapplyl
             (fapply (car fl) a
                     (lambda ()
       (throw 'fapplyl
 (fapplyl (cdr fl) a fail))))))))

(defun fapply (f a fail)
  (let* ((alist (match (cadr f) a fail nil)))
    (apply (cons 'lambda
                 (cons (mapcar 'car alist)
                       (cddr f)))
           (mapcar 'cdr alist))))

(defmacro define (&rest a)
  (let* ((ind (car a))
         (patt (cadr a))
         (body (cddr a))
         (where (cond ((atom patt) patt)
                      ((atom (car patt)) (car patt)))))
    (or (get where ind) (setf (get where ind) '(lambda (e) (cases e))))
    (setf (get where ind)
  `(lambda (e)
     ,(append `(cases e ,(append `(lambda ,patt) body))
      (cddr (caddr (get where ind))))))
    nil))

(setf (get 'star 'cmacro) nil)

(define cmacro (star . (? body))
  `(not (loop ,(append '(seq) body))))

(setf (get 'i2 'cmacro) nil)

(define cmacro (i2 ?p)
  `(seq (1+ p)
(if =0? (1+ (1+ p))
            (seq))))

(setf (get 'move 'cmacro) nil)

(define cmacro (move (? x) (? y))
  `(seq ,(append '(l) (? x))
,(append '(st) (? y))))

(setf (get 'prog 'cmacro) nil)

(define cmacro (prog ((? v)) . (? body))
  `(seq push
(li s)
(move (? v) (i 257))
,(append '(seq) body)
(li s)
(move (i 257) (? v))
i-1
(sti s)))

(setf (get 'fori 'cmacro) nil)

(define cmacro (fori ?from ?to . ?body)
  `(seq ,(append '(li) from)
(while (seq ,(append '(ci) to) llt)
       (seq ,(append '(seq) body) i+1))))

(setf (get 'forj 'cmacro) nil)

(define cmacro (forj ?from ?to . ?body)
  `(seq ,(append '(lj) from)
(while (seq ,(append '(cj) to) llt)
            (seq ,(append '(seq) body) j+1))))

(setf (get 'for 'cmacro) nil)

(define cmacro (for ?v ?from ?to . ?body)
  `(seq ,(append '(l) from) ,(append '(st) v)
(while (seq ,(append '(c) to) llt)
       (seq ,(append '(seq) body)
    ,(append '(1+) v)
    ,(append '(l) v)))))
||#


#||
(setq typical '(seq c=0 binary enable v=0))

(setq typ1 '(alt (seq <0? (1+ m))
                 (1- b))
      m 100
      b 101)

(setq typ2 '(not (loop (seq <0? (1+ m)))))

(setq typ3 '(star (seq (li s) ~=0? pop)))

(setq typ3 '(not (loop (seq (li s) ~=0? pop))))

(setq incr
      '(seq (li \# 0)
            c=1
            (while c=1?
              (seq (l i n) (+ \# 0) (st i n))))
      n 32)

(setq sum
      '(seq (l \# 0)
            li
            (while (seq (ci n) ~=?)
              (seq (+ i A) i+1)))
      A 29)

(setq mult
      '(seq (l x) (st xp)
            (l y) (st y0p)
            (l \# 0) (st y1p) (st z0) (st z1)
            (while (seq (lsr xp) ~=?)
              (seq c=0 (l z0) (+ y0p) (st z0)
                   (l z1) (+ y1p) (st z1)
                   (asl y0p) (rl y1p)))))

(setq x 1 xp 2
      y 3 y0p 4
      y1p 5 z1 6
      z0 7)

(setq masktable
      '(compile '(seq 128 64 32 16 8 4 2 1) 0 0)
      p 8)

(setq testb
      '(seq push
            (land \# 7)
            (li a)
            pop
            (3 lsr)
            (lj a)
            (l @j p)
            (land i masktable)
            return))

(setq setb
      '(seq push
            (land \# 7)
            (li a)
            pop
            (3 lsr)
            (lj a)
            (l @j p)
            (lor i masktable)
            (st @j p)
            return))

;;; Routines for the Universal Product Code Wand.  Requires 88 bytes+table.
(setq upctable
      (compile '(seq 13 25 19 61 35 49 47 59 55 11) 0 0))

(setq
 code 11
 digit 12
 mq 13
 upcwand
 '(alt
   (seq (fori (\# 6) (\# 12)            ; complement patterns of right 6 upc digits.
              (l i code)
              (lxor \# 127)
              (st i code))
        (fori (\# 0) (\# 12)
              (l i code)
              (not
               (forj (\# 0) (\# 10)
                     (c j upctable)
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
              (+ i digit)               ; loop cotrol clears carry.
              i+1)                      ; only every other one.
        (lxor \# 15)                    ; select low decimal digit.
        =0?                            ; fails if non-zero.
        return)
   (seq break                           ; signal failure.
        return)))
||#

(defclass segment ()
  ((label :accessor label :initarg :label)
   (byte-count :accessor byte-count :initarg :byte-count)
   ;;; FIXME: should page-category be a subclassing relation?
   (page-category :accessor page-category :initarg :page-category
		  :documentation "Category of address space this segment is
intended to occupy. \"Ordinary\" memory is denoted by NIL, other types include
:ZERO-PAGE")
   
   (code-vector :accessor code-vector :initarg :code-vector)))

(defparameter *comfy-functions*
  (list (cons '1+ #'cl:1+)
	(cons '1- #'cl:1-)
	(cons '+  #'cl:+)
	(cons '-  #'cl:-)
	(cons '*  #'cl:*)
	(cons 'low #'(lambda (num) (ldb (byte 8 0) num)))
	(cons 'high #'(lambda (num) (ldb (byte 8 8) num)))))

(defun eval-zp-expression (expr symbol-table)
  (labels ((check-range (val)
	     (cl:if (<= 0 val 255)
		    val 
		    (error "Bad zero-page value ~A from expression ~A"
			   val expr)))
	   (valid-number-or-symbolic (expr)
	     (let ((value (eval-address-expression expr symbol-table)))
	       (cl:if (numberp value)
		      (check-range value)
		      (cond
			((and (symbolp expr) (eq value :ZERO-PAGE))
			 expr) ; earlier declared zero-page by user
			((and (symbolp expr) 
			      (consp value) (eq (car expr) :ZERO-PAGE))
			 (cadr value)) ; declared to something 
			               ; asserted zp
			(t value))))))
    (cond
      ((numberp expr) (list :ZERO-PAGE (check-range expr)))
      ((symbolp expr) (list :ZERO-PAGE (valid-number-or-symbolic expr)))
      ((eq (car expr) :ZERO-PAGE) ; user asserting zero-pageness
       (list :ZERO-PAGE (valid-number-or-symbolic (cadr expr))))
      (t (list :ZERO-PAGE (valid-number-or-symbolic expr))))))

(defun eval-absolute-expression (expr symbol-table)
  (labels ((check-range (val)
	     (cl:if (<= -32768 val 65535)
		    val 
		    (error "Bad absolute value ~A from expression ~A"
			   val expr)))
	   (valid-number-or-symbolic (expr)
	     (let ((value (eval-address-expression expr symbol-table)))
	       (cl:if (numberp value)
		      (check-range value)
		      value))))
    (cond
      ((numberp expr) (list :ABSOLUTE (check-range expr)))
      ((symbolp expr) (list :ABSOLUTE (valid-number-or-symbolic expr)))
      ((eq (car expr) :ZERO-PAGE) ; user asserting zero-pageness
       (list :ABSOLUTE (valid-number-or-symbolic (cadr expr))))
      ((eq (car expr) :ABSOLUTE) 
       (list :ABSOLUTE (valid-number-or-symbolic (cadr expr))))
      (t (list :ABSOLUTE (valid-number-or-symbolic expr))))))

(defun eval-address-expression (expr symbol-table)
  "Reduce an address expression (if possible), given the information in 
SYMBOL-TABLE."
  (cond
    ((numberp expr) expr)
    ((symbolp expr)
     (multiple-value-bind (value present) 
	 (gethash expr symbol-table)
       (cl:if present
	      value
	      expr)))
    ((eq (car expr) :ABSOLUTE)
     (eval-absolute-expression expr symbol-table))
;;     (let ((value (eval-address-expression (cadr expr) symbol-table)))
;;       (cl:if (numberp value)
;;	      value
;;	      expr)))
    ((eq (car expr) :ZERO-PAGE)
     (eval-zp-expression expr symbol-table))
;;     (let ((value (eval-address-expression (cadr expr) symbol-table)))
;;       (cl:if (numberp value)
;;	      (cl:if (<= 0 value 255)
;;		     value
;;		     (error "Bad zero-page expression ~A." expr))
;;	      expr)))
    ((eq (car expr) 'LISP)
     (cl:eval (cadr expr)))
    ((symbolp (car expr))
     (let ((func (cdr (assoc (car expr) *comfy-functions*))))
       (cl:if (functionp func)
	      (let ((arglist (mapcar #'(lambda (exp) 
					 (eval-address-expression
					  exp symbol-table)) 
				     (rest expr))))
		(cl:if (every #'numberp arglist)
		       (apply func arglist)
		       expr))
	      expr)))))


(defun eval-immediate-expression (expr symbol-table)
  "Reduce a (one-byte) immediate expression (if possible), given 
the information in SYMBOL-TABLE."
  (cond
    ((numberp expr) 
     (cl:if (<= -128 expr 255)
	    expr
	    (error "Bad immediate value ~A." expr)))
    ((symbolp expr)
     (multiple-value-bind (value present) 
	 (gethash expr symbol-table)
       (cl:if present
	      value
	      expr)))
    ((eq (car expr) :ABSOLUTE)
     (let ((value (eval-address-expression (cadr expr) symbol-table)))
       (cl:if (numberp value)
	      (cl:if (<= 0 value 255)
		     value
		     (error "Absolute address does not fit in one byte ~A." expr))
	      expr)))
    ((eq (car expr) :ZERO-PAGE)
     (let ((value (eval-address-expression (cadr expr) symbol-table)))
       (cl:if (numberp value)
	      (cl:if (<= 0 value 255)
		     value
		     (error "Bad zero-page expression ~A." expr))
	      expr)))
    ((eq (car expr) 'LISP)
     (let ((value (cl:eval (cadr expr))))
       (cl:if (<= -128 value 255)
	      value
	      (error "Lisp expression does not fit in one byte ~A." expr))))
    ((symbolp (car expr))
     (let ((func (cdr (assoc (car expr) *comfy-functions*))))
       (cl:if (functionp func)
	      (let ((arglist (mapcar #'(lambda (exp) 
					 (eval-address-expression
					  exp symbol-table)) 
				     (rest expr))))
		(cl:if (every #'numberp arglist)
		       (let ((value (apply func arglist)))
			 (cl:if (<= -128 value 255)
				value
				(error "Function call ~A value ~D does not fit in one byte."
				       expr value)))
		       expr))
	      expr)))))

(defmacro equ (name value)
  (let ((val (gensym)))
    `(let ((,val ,value))
      (multiple-value-bind (current-value present)
	  (gethash ',name *symbol-table*)
	(cl:when present
	  (cl:if (eql ,val current-value)
		 (warn "Redundant definition for ~A" ',name)
		 (warn "Redefining ~A from ~D to ~D" 
		       ',name current-value ,val)))
	(setf (gethash ',name *symbol-table*) ,val)))))


