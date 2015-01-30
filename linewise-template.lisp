;;;; LINEWISE-TEMPLATE
;;;;
;;;; Copyright (c) 2015, by Boris Smilga
;;;; All rights reserved.
;;;; Distributed under the BSD 3-clause license (see file LICENSE)

(defpackage #:linewise-template
  (:use #:cl #:cl-ppcre)
  (:export #:*directive-circumfix* #:*directive-escape*
           #:*directive-base-packages* #:process-template
           #:*source-stream* #:*source-line-count*))

(in-package #:linewise-template)


;; Some useful macros and functions ;;

(defmacro bind-keys-and-suffix (spec form &body body)
  (let ((keys-spec (butlast spec))
        (suffix (first (last spec)))
        (keys (gensym "KEYS"))
        (k (gensym "K"))
        (v (gensym "V")))
    `(loop for ,suffix :on ,form :by #'cddr
           for (,k ,v) := ,suffix
           while (and (cdr ,suffix) (keywordp ,k))
           collect ,k :into ,keys
           collect ,v :into ,keys
           finally (return
                     (destructuring-bind (&key ,@keys-spec) ,keys
                       ,@body)))))

(defmacro if/bind ((vars cond) seq &optional alt)
  `(multiple-value-bind ,(if (listp vars) vars `(,vars)) ,cond
     (if ,(if (listp vars) (first vars) vars) ,seq ,alt)))

(defmacro cond/bind (clause &rest more-clauses)
  (multiple-value-bind (vars test body)
      (cond ((eq (second clause) '=)
             (values (first clause) (third clause) (nthcdr 3 clause)))
            ((null (rest clause))
             (let ((test-result (gensym)))
               (values test-result (first clause) (list test-result))))
            (t (values nil (first clause) (rest clause))))
    (let ((alt (and more-clauses `(cond/bind ,@more-clauses))))
      (if vars
          `(if/bind (,vars ,test) (progn ,@body) ,alt)
          `(if ,test (progn ,@body) ,alt)))))

(defmacro def-compiler-var (var)        ; A treatment for gensymoitis
  (let ((base (cl-ppcre:regex-replace-all
                "^[^A-Z]+|.*-|[^A-Z0-9]+$" (symbol-name var) "")))
    `(defvar ,var (gensym ,base))))

(defun symbol= (x y)
  (and (symbolp x) (symbolp y) (string= x y)))

(defun lambda-list-keyword-p (thing &rest additional)
  (or (member thing lambda-list-keywords)
      (member thing additional :test #'symbol=)))

;; Global (usually, file-specific) settings ;;

(defvar *directive-circumfix* nil
  "Prefix or circumfix of directive lines (when in comments etc.): a list of
   0, 1 or 2 ppcre strings.")

(defvar *directive-escape* "@"
  "String to introduce a directive")

(defvar *directive-base-packages* '(#:common-lisp)
  "List of packages which are to be used by the temporary package
   established for reading symbols in directives")

(defmacro with-temp-package (&body body)
  (let ((temp-package (gensym "PKG")))
    `(let ((,temp-package
            (make-package ',temp-package :use *directive-base-packages*)))
       (unwind-protect (let ((*package* ,temp-package)) ,@body)
         (delete-package ,temp-package)))))


;; Directive matching ;;

(let ((current-circumfix *directive-circumfix*)
      (scanner (create-scanner "^(.*)$"))
      (sans-circumfix-reg-offset 0))
  (defun count-registers (tree)
    (if (consp tree)
        (+ (count-registers (car tree)) (count-registers (cdr tree)))
        (case tree ((:register :named-register) 1) (t 0))))
  (defun update-scanner ()
    (let ((prefix (first *directive-circumfix*))
          (suffix (second *directive-circumfix*)))
      (setf current-circumfix
              *directive-circumfix*
            scanner
              (create-scanner
                `(:sequence
                  :start-anchor
                  ,(if prefix `(:regex ,prefix) :void)
                  (:register (:non-greedy-repetition 0 nil :everything))
                  ,(if suffix `(:regex ,suffix) :void)
                  :end-anchor))
            sans-circumfix-reg-offset
              (if prefix
                  (count-registers
                    (cl-ppcre:parse-string (first *directive-circumfix*)))
                  0))))
  (defun sans-circumfix (line)
    (when (not (eq current-circumfix *directive-circumfix*))
      (update-scanner))
    (multiple-value-bind (start end rstarts rends) (scan scanner line)
      (when rstarts
        (subseq line
          (aref rstarts sans-circumfix-reg-offset)
          (aref rends sans-circumfix-reg-offset))))))

(defun directive (re line nargs)
  (if/bind (sans-circumfix (sans-circumfix line))
    (let ((re* `(:sequence :start-anchor
                           ,(or *directive-escape* :void) ,re
                           (:alternation :end-anchor
                                         :whitespace-char-class))))
      (if/bind ((match-start match-end) (scan re* sans-circumfix))
        (let* ((match (subseq sans-circumfix match-start match-end)) 
               (args (let ((*read-eval* nil)
                           (nargs (if (functionp nargs)
                                      (funcall nargs)
                                      nargs)))
                       (loop for i :from 1 :to nargs
                             while match-end
                             with arg
                             do (multiple-value-setq (arg match-end)
                                  (read-from-string sans-circumfix nil nil
                                                    :start match-end))
                             collect arg)))
               (trailer (and match-end (subseq sans-circumfix match-end))))
          (values match args trailer))))))


;; Input spec compiler ;; 

(defun mapcar-to-streams (fn sequence)
  (let* ((streams nil)
         (fn/push (lambda (x)
                    (let ((stream (funcall fn x)))
                      (assert (streamp stream))
                      (push stream streams)
                      stream))))
    (handler-case (mapcar fn/push sequence)
      (serious-condition (c)
        (mapc #'close streams)
        (error c)))))

(defvar *destination* nil)

(defvar *source-stream* nil
  "Reference to the current source stream (the one from which a line most
   recently has been read).")

(defvar *source-line-count* nil
  "Reference to an integer incremented for each line read, and reset for
   each subsequent source stream.")

(defmacro with-input ((input-streams
                       &key file files string strings stream streams
                            (update nil)
                            (backup nil)
                            (circumfix nil circumfix-p)
                            (escape nil escape-p)
                            (base-packages nil base-packages-p))
                      &body body)
  (cond
    ((/= (count-if #'identity
           (list file files stream streams string strings))
         1)
     (error "Exactly one of :FILE :FILES :STRING :STRINGS :STREAM :STREAMS ~
             expected for template source specifier"))
    ((and update (not file))
     (error ":UPDATE is only allowed with :FILE sources")))
  `(let* ((,input-streams
            ,(cond (file `(list (open ,file)))
                   (files `(mapcar-to-streams #'open ,files))
                   (string `(list (make-string-input-stream ,string)))
                   (strings `(mapcar-to-streams
                               #'make-string-input-stream ,strings))
                   (stream `(list ,stream))
                   (streams))))
     (unwind-protect
          (let (,@(when circumfix-p
                    `((*directive-circumfix* ,circumfix)))
                ,@(when escape-p
                    `((*directive-escape* ,escape)))
                ,@(when base-packages-p
                    `((*directive-base-packages* ,base-packages)))
                (*source-stream* nil)
                (*source-line-count* nil))
            ,(if update
                 `(with-open-file (*destination* ,file
                                    :direction :output
                                    :if-exists ,(if backup :rename
                                                    :rename-and-delete))
                    ,@body)
                 `(progn ,@body)))
       ,(unless (or stream streams)
          `(mapc #'close ,input-streams)))))

(defun read-line* (streams)
  (when (consp streams)
    (when (null *source-stream*)
      (setf *source-stream* (first streams)
            *source-line-count* 0))
    (handler-case (read-line *source-stream*)
      (:no-error (line missing-newline-p)
        (declare (ignore missing-newline-p))
        (incf *source-line-count*)
        line)
      (end-of-file ()
        (cond/bind
          (streams* = (rest streams)
           (setf (first streams) (first streams*)
                 (rest streams) (rest streams*)
                 *source-stream* nil)
           (read-line* streams))))
      (t (e) (error e)))))

;; The state engine ;;

(defun process-lines (input prev-residual-line state
                      &key ((:begin begin-handler))
                           ((:end end-handler))
                           ((:directive directive-handler))
                           ((:plain plain-line-handler)))
; (format *trace-output* "In PROCESS-LINES: PREV-RESIDUAL-LINE=~S~%"
;         prev-residual-line)
  (assert (and begin-handler end-handler directive-handler
               plain-line-handler))
  (loop with residual-line := nil
        for line := (or residual-line (read-line* input))
        with state := (funcall begin-handler
                        (or prev-residual-line line) state)
        with tmp-state and tmp-residual-line
;       do (format *trace-output* "In PROCESS-LINES: LINE=~S~%" line)
        if (not line)
          do (setf (getf state :eot) t)
          and return (funcall end-handler nil state)
        else if (multiple-value-setq (tmp-state tmp-residual-line)
                  (funcall end-handler line state))
;         do (format *trace-output*
;                    "In PROCESS-LINES: END-HANDLER => ~S, ~S~%"
;                    tmp-state tmp-residual-line) and
          return (values tmp-state tmp-residual-line)
        else if (multiple-value-setq (tmp-state tmp-residual-line)
                  (funcall directive-handler line state))
;         do (format *trace-output*
;                    "In PROCESS-LINES: DIRECTIVE-HANDLER => ~S, ~S~%"
;                    tmp-state tmp-residual-line) and
          do (setq state tmp-state residual-line tmp-residual-line)
        else
          do (setq state (funcall plain-line-handler line state))
             (setq residual-line nil)))

(defun process-atomic (input residual-line state
                       &key ((:begin begin-handler))
                            ((:end end-handler))
                       &allow-other-keys)
; (format *trace-output* "In PROCESS-ATOMIC: RESIDUAL-LINE=~S~%"
;         residual-line)
  (assert (and begin-handler end-handler))
  (assert residual-line)
  (funcall end-handler residual-line
           (funcall begin-handler residual-line state)))

;; Directive spec compiler ;;

(defgeneric compile-spec (selector sibling-selectors action detail))

(defun validate-selector (selector)
  (if (or (typep selector '(or string symbol character))
          (and (consp selector)
               (member (car selector) '(:block :after :atomic))
               (consp (cdr selector))
               (typep (cadr selector) '(or string symbol character))))
      selector
      (error "Invalid selector: ~S" selector)))

(defun validate-destination (destination)
  (if (consp destination)
      (case (and (consp (cdr destination)) (null (cddr destination))
                 (car destination))
        ((:stream) (values (cadr destination) nil nil))
        ((:var) (values nil (cadr destination) nil))
        ((:function) (values nil nil (cadr destination)))
        (t (error "Invalid destination: ~S" destination)))
      (values destination nil nil)))

(defun name+nargs (selector)
  (values (second selector)
          (let ((arg-spec (cddr selector))
                (nargs 0)
                (nargs-infty nil))
            (flet ((pop-and-count-vars ()
                     (loop initially (if (lambda-list-keyword-p
                                           (car arg-spec) '&trailer)
                                         (pop arg-spec))
                           until (or (endp arg-spec)
                                     (lambda-list-keyword-p
                                       (car arg-spec) '&trailer))
                           do (pop arg-spec)
                           count 1)))
              (when (eq (car arg-spec) '&whole)
                (setq arg-spec (cddr arg-spec)))
              (incf nargs (pop-and-count-vars))
              (when (eq (car arg-spec) '&optional)
                (incf nargs (pop-and-count-vars)))
              (when (eq (car arg-spec) '&rest)
                (setq nargs-infty t)
                (setq arg-spec (cddr arg-spec)))
              (when (eq (car arg-spec) '&key)
                (incf nargs (* (pop-and-count-vars) 2))
                (setq nargs-infty (eq (car arg-spec) '&allow-other-keys)))
              (if nargs-infty lambda-parameters-limit nargs)))))

(defun block-selector (selector)
  (when (and (consp selector) (eq (first selector) :block))
    (name+nargs selector)))

(defun after-selector (selector)
  (when (and (consp selector) (eq (first selector) :after))
    (name+nargs selector)))

(defun atomic-selector (selector)
  (if (consp selector)
      (and (eq (first selector) :atomic) (name+nargs selector))
      (values selector 0)))

(defun disallow-atomic (selector action)
  (when (atomic-selector selector)
    (error "Action ~S is not compatible with atomic selector ~S"
           action selector)))

(def-compiler-var $line$)

(def-compiler-var $residual-line$)

(def-compiler-var $state$)

(defun compile-check-eot (selector)
  (unless (atomic-selector selector)
    `(when (not ,$line$)
       ,(when (block-selector selector)
          `(warn "End of input before end of ~A" ',selector))
       t)))

(defun directive-regex (begin/end names)
  (if (null names)
      `(:regex "(?!o)o")                ; This regex never matches
      `(:sequence ,@(if begin/end `(,begin/end (:regex "\\s+")))
                  ,(if (consp names)
                       (if (consp (rest names))
                           `(:alternation ,@names)
                           (first names))
                       names))))

(defun compile-check-end-directive (selector sibling-selectors)
  (cond/bind
    (block-name = (block-selector selector)
     `(directive ',(directive-regex "END" (string block-name))
                 ,$line$ 0))
    (after-name = (after-selector selector)
     (let ((outer-block
             (if/bind (name (block-selector (car sibling-selectors)))
               (string name))))
       (loop for selector :in (cdr sibling-selectors)
             with name
             if (setq name (block-selector selector))
               collect (string name) :into blocks
             else if (or (setq name (after-selector selector))
                         (setq name (atomic-selector selector)))
               collect (string name) :into no-blocks
             finally
               (return
                 `(and (directive '(:alternation
                                    ,(directive-regex "END" outer-block)
                                    ,(directive-regex "BEGIN" blocks)
                                    ,(directive-regex nil no-blocks))
                                  ,$line$ 0)
                       (setq ,$residual-line$ ,$line$))))))
    ((atomic-selector selector)
     t)))

(defun compile-check-end (selector sibling-selectors)
  `(or ,(compile-check-eot selector)
       ,(compile-check-end-directive selector sibling-selectors)))

(def-compiler-var $dest$)

(defun compile-copy-directive (selector preserve)
  (when (and (or (eq selector t) (block-selector selector))
             preserve)
    `(let ((,$dest$ (getf ,$state$ :destination)))
       (when (and ,$line$ ,$dest$)
         (write-line ,$line$ ,$dest$)))))

(defun compile-write-value (value)
  (let (($val (gensym "VAL")))
    `(let ((,$val ,value)
           (,$dest$ (getf ,$state$ :destination)))
       (when (and ,$val ,$dest$)
         (princ ,$val ,$dest$)
         (fresh-line ,$dest$)))))

(defun compile-yield-dest (place fn)
  (when (or place fn)
    `(let ((,$dest$ (getf ,$state$ :destination)))
       (when (typep ,$dest$ 'string-stream)
         (,@(cond (place `(setf ,place)) (fn `(funcall ,fn)))
          (get-output-stream-string ,$dest$))))))

(defun get-destination (state)
  (loop for state* := state then (getf state* :outer-state)
        while state*
        thereis (getf state* :destination)))

(defun compile-push-state (selector destination default-destination)
  (let (($state* (gensym "STATE")))
    `(let ((,$state* (copy-list ,$state$)))
       ,(let ((set-stream
                (if (or destination (not default-destination))
                    `(setf (getf ,$state* :destination) ,destination)
                    `(or (getf ,$state* :destination)
                         (setf (getf ,$state* :destination)
                               (or ,(if (null selector)
                                        '*destination*
                                        `(get-destination ,$state$))
                                   ,default-destination))))))
          (if (or destination default-destination)
              `(assert (output-stream-p ,set-stream))
              set-stream))
       (setf (getf ,$state* :outer-state) ,$state$)
       (setf ,$state$ ,$state*))))

(defun compile-pop-state (&optional (inner t))
  (let ((pop-expr `(setf ,$state$ (getf ,$state$ :outer-state))))
    (if inner pop-expr
        `(if (getf ,$state$ :eot)
             ,(compile-yield-dest nil 'identity)
             ,pop-expr))))

(def-compiler-var $input$)

(defun selector-lambda-list (selector $trailer)
  (let ((ll0 (cddr selector)))
    (if/bind (trailer-var (member '&trailer ll0 :test #'symbol=))
      (let ((ll1 (ldiff ll0 trailer-var))
            (trailer-var-bind (list (cadr trailer-var) $trailer)))
        (append ll1
                (if (member '&aux ll1)
                    (list trailer-var-bind)
                    (list '&aux trailer-var-bind))))
      ll0)))

(defun compile-directive-handler (subs selector cousin-selectors #|action|#)
  (let ((sibling-selectors (append (if (block-selector selector)
                                       (list selector)
                                       (or cousin-selectors (list nil)))
                                   (mapcar #'car subs)))
        ($handler (gensym "HNDLR"))
        ($args (gensym "ARGS"))
        ($trailer (gensym "TRAIL")))
    (mapc #'validate-selector sibling-selectors)
    (flet ((sub-handler (selector action detail)
             (let ((call-expr `(,(if (atomic-selector selector)
                                     'process-atomic
                                     'process-lines)
                                 ,$input$ ,$residual-line$ ,$state$
                                 ,@(compile-spec selector sibling-selectors
                                                 action detail))))
               `(lambda (,$residual-line$ ,$state$ ,$args ,$trailer)
;                 (format *trace-output* "In sub-handler for ~S x ~S: ~
;                         $RESIDUAL-LINE$=~S $ARGS=~S~%"
;                         ',(and selector (subseq selector 0 2))
;                         ',action ,$residual-line$ ,$args)
                  ,(if (and (consp selector) (cddr selector))
                       `(destructuring-bind
                            ,(selector-lambda-list selector $trailer) ,$args
                          ,call-expr)
                       call-expr))))
           (handler-setter-regex-maker (name nargs handler)
             (let (($pos (gensym "POS")))
               `(list :sequence
                  ,(string name)
                  (list :filter
                    (lambda (,$pos)
                      (setq ,$handler ,handler
                            ,$args ,nargs)
                      ,$pos))))))
      (loop for (selector action . detail) :in subs
            for handler := (sub-handler selector action detail)
            with name and nargs
            if (multiple-value-setq (name nargs) (block-selector selector))
              collect (handler-setter-regex-maker name nargs handler)
                :into blocks
            else if (or (multiple-value-setq (name nargs)
                          (after-selector selector))
                        (multiple-value-setq (name nargs)
                          (atomic-selector selector)))
              collect (handler-setter-regex-maker name nargs handler)
                :into no-blocks
            finally
              (return
                (let (($re (gensym "RE"))
                      ($name (gensym "NAME")))
                  `(lambda (,$line$ ,$state$)
;                    (format *trace-output*
;                            "In directive handler for ~S x ~S: $LINE$=~S~%"
;                            ',(and selector (subseq selector 0 2))
;                            ,action
;                            ,$line$)
                     (let* ((,$handler nil)
                            (,$args 0)
                            (,$re (list :alternation
                                    (directive-regex
                                      "BEGIN" (list ,@blocks))
                                    (directive-regex
                                      nil (list ,@no-blocks)))))
                       (cond/bind
                        ((,$name ,$args ,$trailer) =
                             (directive ,$re ,$line$ (lambda () ,$args))
                         (assert ,$handler)
                         (multiple-value-prog1
                             (funcall ,$handler ,$line$ ,$state$
                                      ,$args ,$trailer)
                           (setf ,$handler nil ,$args 0))))))))))))

(defmethod compile-spec (selector sibling-selectors (action (eql :copy))
                         detail)
  (disallow-atomic selector action)
  (bind-keys-and-suffix (((:to destination))
                         ((:do expr)) preserve-directives subs)
      detail
    (multiple-value-bind (dest-stream dest-var dest-fn)
        (validate-destination destination)
      `(:begin (lambda (,$line$ ,$state$)
                 ,(compile-push-state selector dest-stream
                                      '(make-string-output-stream))
                 ,(compile-copy-directive t preserve-directives)
                 ,$state$)
          :end (lambda (,$line$ ,$state$ &aux (,$residual-line$ nil))
                 (when ,(compile-check-end selector sibling-selectors)
                   ,(compile-copy-directive selector preserve-directives)
                   ,(compile-yield-dest dest-var dest-fn)
                   ,expr
                   (values ,(compile-pop-state (or selector destination))
                           ,$residual-line$)))
    :directive ,(compile-directive-handler subs selector sibling-selectors)
        :plain (lambda (,$line$ ,$state$)
                 (write-line ,$line$ (getf ,$state$ :destination))
                 ,$state$)))))

(defmethod compile-spec (selector sibling-selectors (action (eql :replace))
                         detail)
  (let ((atomic (atomic-selector selector)))
    (bind-keys-and-suffix (((:with replacement))
                           ((:do expr)) preserve-directives subs)
        detail
      `(:begin (lambda (,$line$ ,$state$)
                 ,(compile-copy-directive t preserve-directives)
                 ,(if atomic $state$
                      (compile-push-state selector nil nil)))
          :end (lambda (,$line$ ,$state$ &aux (,$residual-line$ nil))
                 (when ,(compile-check-end selector sibling-selectors)
                   ,(unless atomic
                      (compile-pop-state))
                   ,(compile-write-value replacement)
                   ,(compile-copy-directive selector preserve-directives)
                   ,expr
                   (values ,$state$ ,$residual-line$)))
    :directive ,(compile-directive-handler subs selector sibling-selectors)
        :plain (lambda (,$line$ ,$state$) ,$state$)))))

(defmethod compile-spec (selector sibling-selectors (action (eql :transform))
                         detail)
  (disallow-atomic selector action)
  (bind-keys-and-suffix (((:by transform-fn)) ((:to destination))
                         ((:do expr)) preserve-directives subs)
      detail
    (assert transform-fn)
    (multiple-value-bind (dest-stream dest-var dest-fn)
        (validate-destination destination)
      (let (($transformed (gensym "VAL")))
        `(:begin (lambda (,$line$ ,$state$)
                   ,(compile-push-state selector dest-stream
                                        '(make-string-output-stream))
                   ,(compile-copy-directive t preserve-directives)
                   ,(compile-push-state t '(make-string-output-stream) nil))
            :end (lambda (,$line$ ,$state$ &aux (,$residual-line$ nil))
                   (when ,(compile-check-end selector sibling-selectors)
                     (let ((,$transformed
                             ,(compile-yield-dest nil transform-fn)))
                       ,(compile-pop-state)
                       ,(cond (dest-var
                               `(setf ,dest-var ,$transformed))
                              (dest-fn
                               `(funcall ,dest-fn ,$transformed))
                              (t (compile-write-value $transformed)))
                       ,(compile-copy-directive selector preserve-directives)
                       ,expr
                       (values ,(compile-pop-state (or selector destination))
                               ,$residual-line$))))
      :directive ,(compile-directive-handler subs selector sibling-selectors)
          :plain (lambda (,$line$ ,$state$)
                   (write-line ,$line$ (getf ,$state$ :destination))
                   ,$state$))))))

(defmethod compile-spec (selector sibling-selectors (action (eql :discard))
                         detail)
  (bind-keys-and-suffix (((:do expr)) preserve-directives subs) detail
    (compile-spec selector sibling-selectors :replace
                  `(:with nil :do ,expr
                    :preserve-directives ,preserve-directives
                    ,@subs))))

(defmethod compile-spec :around (selector sibling-selectors action detail)
  (if (and selector (atomic-selector selector))
      (bind-keys-and-suffix (&allow-other-keys subs) detail
        (if (null subs)
            (let ((handlers (call-next-method)))
              (remf handlers :directive)
              (remf handlers :plain)
              handlers)
            (error "Subspecs not compatible with atomic selector ~S"
                   selector)))
      (call-next-method)))


;; The entrypoint ;;

(defmacro process-template (spec)
  "Process the template specified by SPEC, which must have the following
   syntax:

                 <SPEC> ::= (<SOURCE-SPEC> <ACTION-AND-OPTIONS>
                             [ <SUBSPEC>* ])

          <SOURCE-SPEC> ::= ([[ {<SOURCE-STREAM-SPEC>}1 | <SOURCE-OPTS>* ]])
   
   <SOURCE-STREAM-SPEC> ::= :FILE <PATH> [[ <UPDATE-OPTS>* ]] |
                            :FILES <PATHS> |
                            :STRING <STRING> | :STRINGS <STRINGS> |
                            :STREAM <STREAM> | :STREAMS <STREAMS>

          <UPDATE-OPTS> ::= :UPDATE <BOOLEAN> | :BACKUP <BOOLEAN>

          <SOURCE-OPTS> ::= :CIRCUMFIX <REGEXP-PARTS> | :ESCAPE <STRING> |
                            :BASE-PACKAGES <PACKAGES>

   <ACTION-AND-OPTIONS> ::= :COPY [[ <COPY-OPTS>* ]] |
                            :TRANSFORM [[ <TRANSFORM-OPTS>* ]] |
                            :REPLACE [[ <REPLACE-OPTS>* ]] |
                            :DISCARD [[ <DISCARD-OPTS>* ]]

            <COPY-OPTS> ::= :TO <DESTINATION> | <COMMON-OPTS>

       <TRANSFORM-OPTS> ::= :BY <FUNCTION> | :TO <DESTINATION> |
                            <COMMON-OPTS>

         <REPLACE-OPTS> ::= :WITH <STRING-OR-NIL> | <COMMON-OPTS>

         <DISCARD-OPTS> ::= <COMMON-OPTS>

          <COMMON-OPTS> ::= :DO <EXPRESSION> |
                            :PRESERVE-DIRECTIVES <BOOLEAN>

              <SUBSPEC> ::= (<SELECTOR> <ACTION-AND-OPTIONS>
                             [ <SUBSPEC>* ])

             <SELECTOR> ::= <NAME> |
                            (:ATOMIC <NAME> [ <ARGS> [ <TRAILER-ARG> ]]) |
                            (:BLOCK <NAME> [ <ARGS> [ <TRAILER-ARG> ]]) |
                            (:AFTER <NAME> [ <ARGS> [ <TRAILER-ARG> ]])

          <DESTINATION> ::= NIL | <STREAM> |
                            (:VAR <VAR>) | (:FN <FUNCTION>) 

                 <NAME> ::= <string designator>

                 <ARGS> ::= <destructuring lambda list>

          <TRAILER-ARG> ::= &TRAILER <VAR>  ; &TRAILER is matched by name

                  <VAR> ::= <symbol>

   <PATH> | <STRING> | <STRING-OR-NIL> |    ; Evaluated to produce a single
       <STREAM> | <BOOLEAN> | <FUNCTION>    ; value of the specified type
                        ::= <expression>

   <PATHS> | <STRINGS> | <STREAMS> |        ; Evaluated to produce a list of
             <PACKAGES> ::= <expression>    ; values of the specified type

         <REGEXP-PARTS> :: <expression>     ; Evaluated to produce a list of
                                            ; 0, 1 or 2 strings, conjoined
                                            ; to form a ppcre

   The sources specified in <SOURCE-SPEC> are read from by READ-LINE and the
   resulting lines processed in a dynamic environment where
   *DIRECTIVE-CIRCUMFIX*, *DIRECTIVE-ESCAPE* and *DIRECTIVE-BASE-PACKAGES*
   are bound to the values of the corresponding <SOURCE-OPTS> (when
   provided), *SOURCE-STREAM* is bound to the current source stream, and
   *SOURCE-LINE-COUNT* to the number of lines read from that stream.

   Lines are processed according to <ACTION-AND-OPTIONS> applying either to
   the whole source (those outside of any <SUBSPEC>), or to some part of the
   source delimited by “directives”.  A directive is a line that has a
   prefix and suffix matching respectively the first and second element of
   *DIRECTIVE-CIRCUMFIX* (unless null), and a middle portion beginning with
   the string *DIRECTIVE-ESCAPE* (unless null), followed by keywords given
   by <SELECTOR>s of applicable <SUBSPEC>s, followed by zero or more
   whitespace-separated Lisp expressions, followed by zero or more trailer
   characters.  In the following, we give examples of directives for
   *DIRECTIVE-ESCAPE* = \"@\" and *DIRECTIVE-CIRCUMFIX* = NIL; X stays for
   arbitrary names.

   A <SUBSPEC> with a (:BLOCK X ...) selector applies to any part of the
   source starting with a @BEGIN X directive and an ending with an @END X
   directive.

   A <SUBSPEC> with an (:AFTER X ...) selector applies to any part of the
   source starting with an @X directive and ending immediately before the
   start of any sibling <SUBSPEC>, or before the end of its parent
   <SUBSPEC>, whichever comes first.

   A <SUBSPEC> with an (:ATOMIC X ...) selector applies to just the
   directive line.  A plain X selector is shorthand for (:ATOMIC X).

   Nested subspecs take precedence over their parent specs.  Nested subspecs
   are not allowed inside atomic subspecs.  :ATOMIC selectors are
   incompatible with :COPY and :TRANSFORM actions.

   If the <ACTION> is :COPY, affected lines are copied verbatim to
   <DESTINATION>.  If the applicable (sub)spec specifies a non-stream
   destination, an output string-stream is used.  If the destination
   is (:VAR X), the string associated with the stream is assigned to the
   variable X once all affected lines have been copied.  If the destination
   is (:FN X), the function to which X evaluates is called on the associated
   string for side effects once all affected lines have been copied.

   If the (sub)spec does not specify any <DESTINATION>, it is inherited from
   the parent spec; for the topmost <SPEC> without an explicit destination,
   and for a <SPEC> that specifies :TO NIL, an output string-stream is used.
   However, if <SOURCE-STREAM-SPEC> includes the option :UPDATE T, the
   destination shall instead be a stream writing to a new version of the
   input file; additionally, the option :BACKUP T causes the prior version
   of the file to be backed up as if by (OPEN ... :IF-EXISTS :RENAME).

   If the <ACTION> is :TRANSFORM, affected lines are copied to a temporary
   string, the string is passed to the specified function, and the value
   returned by the function is written to the destination as if by :COPY.
   Subspecs of this spec shall inherit as destination an output stream
   writing to the temporary string.

   If the <ACTION> is :REPLACE, affected lines are not copied.  Instead,
   the specified value (unless null) is written to the destination inherited
   from the parent spec.  :DISCARD is a shorthand for :REPLACE :WITH NIL.

   If <SELECTOR> includes some <ARGS>, they are expected to form a
   destructuring lambda list.  In this case, Lisp expressions are read from
   the directive line after the directive name: until the end of the line if
   <ARGS> contains a &REST and no &KEY keywords, or until the maximum
   possible number of arguments needed to satisfy the lambda list is
   obtained.  The list of expressions is matched against <ARGS> as if by
   DESTRUCTURING-BIND.  Lisp expressions inside the selector's <SUBSPEC> are
   then evaluated in a lexcial environment where variables from <ARGS> are
   bound to the data read, and the variable from <TRAILER-ARG> (if
   specified) is bound to a substring of the directive line after the end of
   the last expression read.  Symbols occuring in the data are interned in a
   temporary package which inherits all external symbols from
   *DIRECTIVE-BASE-PACKAGES*.

   The option :DO X causes the expression X to be executed for side-effects
   after all affected lines have been processed.

   The option :PRESERVE-DIRECTIVES T causes the directive(s) delimiting the
   affected lines to be copied to the specified or inherited destination,
   except when both the applicable selector and its parent have :REPLACE
   or :DISCARD actions.

   The value returned by executing PROCESS-TEMPLATE is the string associated
   with the destination stream, if the action in <SPEC> is :COPY or
   :TRANSFORM, the <DESTINATION> is NIL or unspecified, and
   <SOURCE-STREAM-SPEC> does not specify :UPDATE T.  Otherwise, the value is
   NIL."
  (destructuring-bind (input-spec action &rest detail) spec
    `(with-input (,$input$ ,@input-spec)
       (with-temp-package
         (nth-value 0
           (process-lines
             ,$input$ nil nil
             ,@(compile-spec nil nil action detail)))))))
