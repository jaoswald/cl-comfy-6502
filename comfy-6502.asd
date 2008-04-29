;;;; -*- Mode: LISP; Syntax: ANSI-Common-Lisp; Base: 10 -*-
;;;; *************************************************************************
;;;; FILE IDENTIFICATION
;;;;
;;;; Name:          comfy-6502.asd
;;;; Purpose:       ASDF definition file for COMFY-6502
;;;; Programmer:    Joseph A. Oswald, III 
;;;; Date Started:  November 2007
;;;;
;;;; $Id: comfy-6502.asd,v 1.2 2008/03/04 14:02:36 oswaldj Exp $
;;;;
;;;; This file, part of comfy-6502, is Copyright (c) 2007 
;;;; by Joseph A. Oswald, III
;;;;
;;;; comfy-6502.lisp is based on code from Henry G. Baker, and
;;;; comfy-6502 users are granted the rights to distribute and use this 
;;;; software as governed by the terms of the ACM Software License
;;;; Agreement. (See ACM-LICENSE.txt)
;;;; *************************************************************************

(asdf:defsystem :comfy-6502
  :name "comfy-6502"
  :version "2008.03.04"
  :author "Henry G. Baker and Joseph A. Oswald, III <josephoswald@gmail.com>"
  :maintainer "Joseph A. Oswald, III <josephoswald@gmail.com>"
  :licence "ACM Software License Agreement"
  :description "Baker's COMFY Assembler for 6502"
  :long-description "A 'medium-level' assembly language for the 6502 CPU, designed by Henry G. Baker, converted to Common Lisp and improved by Joseph A. Oswald, III."
  :components
  ((:file "6502-opcodes")
   (:file "comfy-6502" :depends-on ("6502-opcodes"))))

(asdf:defsystem :comfy-6502-test
  :name "comfy-6502-test"
  :version "2008.03.04"
  :author "Joseph A. Oswald, III <josephoswald@gmail.com>"
  :maintainer "Joseph A. Oswald, III <josephoswald@gmail.com>"
  :description "Tests for comfy-6502"
  :components
  ((:file "comfy-tests"))
  :depends-on (#+sbcl "sb-rt" #-sbcl "rt" "comfy-6502"))

(asdf:defsystem :6502-test
  :name "6502-test"
  :version "2008.03.04"
  :author "Joseph A. Oswald, III <josephoswald@gmail.com>"
  :maintainer "Joseph A. Oswald, III <josephoswald@gmail.com>"
  :description "Tests for 6502 opcodes"
  :components
  ((:file "6502-tests"))
  :depends-on (#+sbcl "sb-rt" #-sbcl "rt" "comfy-6502"))
