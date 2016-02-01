;;;; -*- lisp -*-

(defpackage #:linewise-template-system
  (:use #:cl #:asdf))
(in-package #:linewise-template-system)

(defsystem #:linewise-template
  :name "Linewise-template"
  :author "Boris Smilga <boris.smilga@gmail.com>"
  :maintainer "Boris Smilga <boris.smilga@gmail.com>"
  :licence "BSD-3-Clause"
  :description "Linewise file/stream processor for code generation etc."
  :depends-on (#:cl-ppcre #:cl-fad)
  :components
    ((:module #:src
        :pathname ""
        :components ((:file "linewise-template")))))
