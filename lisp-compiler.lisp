(in-package #:lisp-compiler)

(defparameter *tail-context* nil)
(defparameter *tail-expression* nil)
(defparameter *functions-stream* nil)
(defparameter *entry-label-emitted* nil)

(defparameter *debug* nil)

(defmacro cle (&rest expr)
  `(compile-lisp-expression ,@expr))

(defmacro at (expr)
  `(apply-transformations ,expr))

(defmacro assertion (cond msg)
  `(if (not ,cond) (error "assertion \"~a\" failed" ,msg)))

(defun curry (function &rest args)
    (lambda (&rest more-args)
      (apply function (append args more-args))))

(defun immediate-rep (x) 
  (cond ((integerp x) (ash x 2))
	((characterp x) (+ (ash (char-int x) 8) 15))
	((null x) 47) ;; empty list also serves as false
	(t 159)))

(defun emit-primitive-call (stream x si env)
  (cond
    ((equal (first x) 'add1)
     (progn (emit-expr stream (second x) si env)
	    (format stream "  addl $~a, %eax~%" (immediate-rep 1))))
    ((equal (first x) 'sub1)
     (progn (emit-expr stream (second x) si env)
	    (format stream "  subl $~a, %eax~%" (immediate-rep 1))))
    ((equal (first x) 'integer->char)
     (emit-expr stream (int-char (second x)) si env))
    ((equal (first x) 'char->integer)
     (emit-expr stream (char-int (second x)) si env))
    ((equal (first x) 'zero?)
     (progn (emit-expr stream (second x) si env) 
	    (format stream "  cmpl $0, %eax~%")
	    (format stream "  movl $0, %eax~%")
	    (format stream "  sete %al~%")
	    (format stream "  sall $7, %eax~%")
	    (format stream "  orl $31, %eax~%")))
    ((equal (first x) 'null?)
     (progn (emit-expr stream (second x) si env) 
	    (format stream "  cmpl $47, %eax~%")
	    (format stream "  movl $0, %eax~%")
	    (format stream "  sete %al~%")
	    (format stream "  sall $7, %eax~%")
	    (format stream "  orl $31, %eax~%")))
    ((equal (first x) 'not)
     (progn (emit-expr stream (second x) si env)
	    (if (equal (immediate-rep (second x)) 47)
		(format stream "  movl $159, %eax~%")
		(format stream "  xor $128, %eax~%"))))
    ((equal (first x) 'integer?)
     (progn (emit-expr stream (second x) si env)
	    (format stream "  andl $3, %eax~%")
	    (format stream "  cmpl $0, %eax~%")
	    (format stream "  movl $0, %eax~%")
	    (format stream "  sete %al~%")
	    (format stream "  sall $7, %eax~%")
	    (format stream "  orl $31, %eax~%")))
    ((equal (first x) 'character?)
     (progn (emit-expr stream (second x) si env)
	    (format stream "  andl $255, %eax~%")
	    (format stream "  cmpl $15, %eax~%")
	    (format stream "  movl $0, %eax~%")
	    (format stream "  sete %al~%")
	    (format stream "  sall $7, %eax~%")
	    (format stream "  orl $31, %eax~%")))
    ((equal (first x) 'boolean?)
     (progn (emit-expr stream (second x) si env)
	    (if (equal (immediate-rep (second x)) 47)
		(format stream "  movl $159, %eax~%")
		(progn (format stream "  andl $127, %eax~%")
		       (format stream "  cmpl $31, %eax~%")
		       (format stream "  movl $0, %eax~%")
		       (format stream "  sete %al~%")
		       (format stream "  sall $7, %eax~%")
		       (format stream "  orl $31, %eax~%")))))
    ((equal (first x) '+)
     (emit-higher-arity-primitive 'addl stream (cdr x) si env))
    ((equal (first x) '-)
     (emit-higher-arity-primitive 'subl stream (cdr x) si env))
    ((equal (first x) '*)
     (progn (emit-expr stream (cadr x) si env)
	    (format stream "  movl %eax, ~a(%esp)~%" si)
	    (dolist (v (cddr x))
	      (progn (emit-expr stream v (- si 4) env)
		     (format stream "  imul ~a(%esp), %eax~%" si)
		     (format stream "  sarl $2, %eax~%" si)
		     (format stream "  movl %eax, ~a(%esp)~%" si)))
	    (format stream "  movl ~a(%esp), %eax~%" si)))
    ((or (equal (first x) '=) (equal (first x) 'char=?))
     (progn (emit-expr stream (third x) si env)
	    (format stream "  movl %eax, ~a(%esp)~%" si)
	    (emit-expr stream (second x) (- si 4) env)
	    (format stream "  cmpl ~a(%esp), %eax~%" si)
	    (format stream "  movl $0, %eax~%")
	    (format stream "  sete %al~%")
	    (format stream "  sall $7, %eax~%")
	    (format stream "  orl $31, %eax~%")))
    ((equal (first x) '<)
     (let ((label1 (gensym))
	   (label2 (gensym)))
       (progn (emit-expr stream (third x) si env)
	      (format stream "  movl %eax, ~a(%esp)~%" si)
	      (emit-expr stream (second x) (- si 4) env)
	      (format stream "  cmpl ~a(%esp), %eax~%" si)
	      (format stream "  jl ~a~%" label1)
	      (format stream "  movl $31, %eax~%")
	      (format stream "  jmp ~a~%" label2)
	      (format stream "~a:~%" label1)
	      (format stream "  movl $159, %eax~%")
	      (format stream "~a:~%" label2))))
    ((equal (first x) '>)
     (let ((label1 (gensym))
	   (label2 (gensym)))
       (progn (emit-expr stream (third x) si env)
	      (format stream "  movl %eax, ~a(%esp)~%" si)
	      (emit-expr stream (second x) (- si 4) env)
	      (format stream "  cmpl ~a(%esp), %eax~%" si)
	      (format stream "  jg ~a~%" label1)
	      (format stream "  movl $31, %eax~%")
	      (format stream "  jmp ~a~%" label2)
	      (format stream "~a:~%" label1)
	      (format stream "  movl $159, %eax~%")
	      (format stream "~a:~%" label2))))

    ((equal (first x) 'and)
     (let ((label1 (gensym))
	   (label2 (gensym)))
       (dolist (e (cdr x))
	 (progn (emit-expr stream e si env)
		(format stream "  cmpl $159, %eax~%")
		(format stream "  jne ~a~%" label1)))
       (format stream "  movl $159, %eax~%")
       (format stream "  jmp ~a~%" label2)
       (format stream "~a:~%" label1)
       (format stream "  movl $31, %eax~%")
       (format stream "~a:~%" label2)))

    ((equal (first x) 'or)
     (let ((label1 (gensym))
	   (label2 (gensym)))
       (dolist (e (cdr x))
	 (progn (emit-expr stream e si env)
		(format stream " cmpl $159, %eax~%")
		(format stream " je ~a~%" label1)))
       (format stream "  movl $31, %eax~%")
       (format stream "  jmp ~a~%" label2)
       (format stream "~a:~%" label1)
       (format stream "  movl $159, %eax~%")
       (format stream "~a:~%" label2))) 
))

(defun emit-higher-arity-primitive (primitive stream lst si env)
  (emit-expr stream (car lst) si env)
  (format stream "  movl %eax, ~a(%esp)~%" si)
  (dolist (x (cdr lst))
    (emit-expr stream x (- si 4) env)
    (format stream "  ~a %eax, ~a(%esp)~%" primitive si))
  (format stream "  movl ~a(%esp), %eax~%" si))

(defun emit-expr (stream x si env)
  (unwind-protect
       (progn (if *debug* (format stream "  // emitting asm for expr ~a~%" x))
	      (cond 
		((immediate-exp-p x)
		 (format stream "  movl $~a, %eax~%" (immediate-rep x)))
		((variable-p x)
		 (let ((type (car (cdr (lookup x env))))
		       (offset (cdr (cdr (lookup x env)))))
		   (cond ((equal type 'param)
			  (format stream "  movl ~a(%esp), %eax~%" offset))
			 ((equal type 'free-var)
			  (format stream "  movl ~a(%edi),%eax~%" offset))
			 (t (error (format nil "Unknown variable type (~a) for variable ~a" type x))) )))
		((primitive-call-p x)
		 (emit-primitive-call stream x si env))
		((equal (first x) 'let)
		 (progn (if (not *entry-label-emitted*)
			    (progn (format stream "_lisp_entry:~%")
				   (setq *entry-label-emitted* t)))
			(emit-let stream (second x) (third x) si env)))
		((equal (first x) 'if)
		 (emit-if stream (second x) (third x) (fourth x) si env))
		((equal (first x) 'cons)
		 (emit-cons stream (second x) (third x) si env))
		((equal (first x) 'car)
		 (emit-car stream (second x) si env))
		((equal (first x) 'cdr)
		 (emit-cdr stream (second x) si env))
		
		((equal (first x) 'make-vector)
		 (emit-make-vector stream (second x) si env))
		((equal (first x) 'vector-ref)
		 (emit-vector-ref stream (second x) (third x) si env))
		((equal (first x) 'vector-set!)
		 (emit-vector-set! stream (second x) (third x) (fourth x) si env))
		
		((equal (first x) 'begin)
		 (emit-begin stream (cdr x) si env))

		((equal (first x) 'make-string)
		 (emit-make-string stream (second x) si env))

		((equal (first x) 'string-ref)
		 (emit-string-ref stream (second x) (third x) si env))

		((equal (first x) 'string-set!)
		 (emit-string-set! stream (second x) (third x) (fourth x) si env))

		((equal (first x) 'labels)
		 (progn (if (not *entry-label-emitted*)
			    (progn (format stream "_lisp_entry:~%")
				   (setq *entry-label-emitted* t)))
			(emit-labels stream (second x) (third x) si env)))

		((equal (first x) 'labelcall)
		 (emit-labelcall stream (second x) (cddr x) si env))

		((equal (first x) 'closure)
		 (emit-closure stream (second x) (cddr x) si env))

		((equal (first x) 'funcall)
		 (if *tail-expression*
		     (emit-funcall-no-tail-call stream (second x) (cddr x) si env)
		     (emit-funcall-no-tail-call stream (second x) (cddr x) si env)))

		((and (listp x) (variable-p (first x)))
		 (emit-expr stream (concatenate 'list (list 'funcall) x) si env))

		((and (listp x) (listp (first x)))
		 (let ((fn (gensym)))
		   (emit-expr stream 
			      (list 'let 
				    (list (list fn (first x)))
				    (concatenate 'list (list fn) (rest x)))
			      si
			      env)))

		(t (error (format nil "Unknown/Undefined operator or function: ~a" (first x))))))
    (if *debug* (format stream "  // end emitting asm for expr ~a~%" x)))
)

(defun lookup (x env) ;;keeping this because the definition of env is likely to change
  (let ((value (assoc (symbol-name x) env :test 'equal)))
    (if value value
	(error (format nil "lookup: failed for ~a" (symbol-name x))))))

(defun compile-lisp-expression (x &optional no-transforms)
  (with-open-file (stream "lisp_entry.s" :direction :output :if-exists :supersede)
    (format stream "  .file  \"lisp_entry.lisp\"~%")
    (format stream "  .text~%")
    (format stream "  .p2align 4,,15~%")
    (format stream ".globl _lisp_entry~%")
    (format stream "  .def    _lisp_entry;  .scl    2;      .type   32;     .endef~%")

    (if no-transforms 
	(emit-expr stream x -4 nil)
	(emit-expr stream (apply-transformations x) -4 nil))
    (format stream "  ret~%"))

  (if *functions-stream* 
      (progn (close *functions-stream*)
	     (setq *functions-stream* nil)))

  (setq *entry-label-emitted* nil))

(defun apply-transformations (expr)
  (let ((val expr))
    (dolist (f (list 
		     #'convert-complex-constants        ;#(1 2 3 4) to (vector 1 2 3 4), "abc" -> (string "abc"),
		                                        ;(1 . 2) to (cons 1 2), etc.
		     #'convert-list-expressions         ;(list 1 2 3)      --> (cons 1 (cons 2 (cons 3 nil)))
		     #'convert-assignments
		     #'convert-vector-expressions
		     #'convert-string-expressions
		     #'convert-lambdas
		     #'build-closures
		     ))
      (setq val (funcall f val)))
    val))

(defun immediate-exp-p (x)
  (or (equal x 't) (integerp x) (characterp x) (null x)))

(defun primitive-call-p (x)
  (let ((op (first x)))
    (or (equal op 'add1)
	(equal op 'sub1)
	(equal op 'integer->char)
	(equal op 'char->integer)
	(equal op 'zero?)
	(equal op 'null?)
	(equal op 'not)
	(equal op 'integer?)
	(equal op 'character?)
	(equal op 'boolean?)
	(equal op '+)
	(equal op '-)
	(equal op '*)
	(equal op '=)
	(equal op 'char=?)
	(equal op '<)
	(equal op '>)
	(equal op 'and)
	(equal op 'or)
)))

;variables should start with an alphabet;
;can be made up of alphanumeric, _, -, ?, # or :
(defun variable-p (x)
  (if (not (symbolp x))
      nil
      (let ((s (symbol-name x)))
	(if (not (alpha-char-p (char s 0)))
	    (return-from variable-p nil)
	    (loop for i from 1 to (1- (length s))
		 do (if (not (or (alpha-char-p (char s i))
				 (digit-char-p (char s i))
				 (equal (char s i) #\_)
				 (equal (char s i) #\-)
				 (equal (char s i) #\?)
				 (equal (char s i) #\#)
				 (equal (char s i) #\:)))
			(return-from variable-p nil))))
	t)))

(defun emit-let (stream bindings body si env)
  (labels ((f (bindings si env)
	     (if (null bindings)
		 (progn (if (not (equal (first body) 'begin)) (setq *tail-context* t *tail-expression* t))
			(emit-expr stream body si env)
			(setq *tail-context* nil *tail-expression* nil))
		 (let ((b (car bindings)))
		   (emit-expr stream (second b) si env)
		   (format stream "  movl %eax, ~a(%esp)~%" si)
		   (f (cdr bindings)
		      (- si 4) 
		      (extend-env (symbol-name (first b)) (cons 'param si) env))))))
    (f bindings si env)))

;to handle recursion (to be fixed)
(defun emit-let-recursion (stream bindings body si env)
  (labels ((f (bindings si env)
	     (if (null bindings)
		 (progn (if (not (equal (first body) 'begin)) (setq *tail-context* t *tail-expression* t))
			(emit-expr stream body si env)
			(setq *tail-context* nil *tail-expression* nil))
		 (let* ((b (car bindings))
			(extended-env (extend-env (symbol-name (first b)) (cons 'param si) env)))
		   (format stream "  subl $4, %esp~%")
		   (emit-expr stream (second b) si extended-env)
		   (format stream "  subl $4, %esp~%")
		   (format stream "  movl %eax, ~a(%esp)~%" si)
		   (format stream "  subl $4, %esp~%")
		   (f (cdr bindings)
		      (- si 12) 
		      ;(extend-env (symbol-name (first b)) (cons 'param si) extended-env))))))
		      extended-env)))))
    (f bindings si env)))

(defun extend-env (key value env)
  (push (cons key value) env))

(defun emit-if (stream test conseq altern si env)
  (let ((label0 (gensym))
	(label1 (gensym)))
    (emit-expr stream test si env)

    (if *tail-context* (setq *tail-expression* t))

    (format stream "  cmpl $31, %eax~%")
    (format stream "  je ~a~%" label0)
    (emit-expr stream conseq si env)
    (format stream "  jmp ~a~%" label1)
    (format stream "~a:~%" label0)
    (emit-expr stream altern si env)    
    (format stream "~a:~%" label1)

    (setq *tail-expression* nil)
))

(defun emit-cons (stream car cdr si env)
  (emit-expr stream car si env)
  (format stream "  movl %eax, ~a(%esp)~%" (- si 4))

  (emit-expr stream cdr (- si 4) env)
  (format stream "  movl %eax, ~a(%esp)~%" (- si 8))

  ;using ebx here because gcc complains about too many
  ;memory references for 'mov' otherwise
  (format stream "  movl ~a(%esp), %ebx~%" (- si 8))
  (format stream "  movl %ebx, 4(%esi)~%" (- si 8))

  (format stream "  movl ~a(%esp), %ebx~%" (- si 4))
  (format stream "  movl %ebx, 0(%esi)~%" (- si 4))

  (format stream "  movl %esi, %eax~%")  
  (format stream "  orl $1, %eax~%")    ; tag for cons object is 1
  (format stream "  addl $8, %esi~%"))

(defun emit-car (stream cons-obj si env)
  (emit-expr stream cons-obj si env)
  (format stream "  movl -1(%eax), %eax~%"))

(defun emit-cdr (stream cons-obj si env)
  (emit-expr stream cons-obj si env)
  (format stream "  movl 3(%eax), %eax~%"))

(defun emit-make-vector (stream size si env)
  (emit-expr stream size si env)
  (format stream "  movl %eax, 0(%esi)~%")
  (format stream "  movl %eax, %ebx~%")
  (format stream "  movl %esi, %eax~%")
  (format stream "  orl $2, %eax~%")
  (format stream "  addl $11, %ebx~%")
  (format stream "  andl $-8, %ebx~%")
  (format stream "  addl %ebx, %esi~%"))

(defun emit-vector-ref (stream vector-obj index si env)
  (emit-expr stream index si env)
  (format stream "  movl %eax, %ebx~%")     ; save the index in ebx
  (emit-expr stream vector-obj si env)      ; get vector object's pointer
  (format stream "  subl $-2, %eax~%")      ; extract address of vector object (pointer minus 2)
  (format stream "  addl $4, %ebx~%")       ; add 4 to ebx to skip the word storing the length of the vector
  (format stream "  movl (%eax,%ebx), %eax~%"))

(defun emit-vector-set! (stream vector-obj index obj si env)
  (emit-expr stream index si env)                       ; calculate index (stored by default in eax)
  (format stream "  movl %eax, ~a(%esp)~%" (- si 4))    ; save the index
  (format stream "  addl $4, ~a(%esp)~%" (- si 4))      ; add 4 to skip the word storing the length of the vector

  (emit-expr stream vector-obj (- si 4) env)            ; get vector object's pointer
  (format stream "  movl %eax, ~a(%esp)~%" (- si 8))	; also save the object for returning it at the end

  (format stream "  subl $-2, %eax~%")                  ; extract address of vector object (pointer minus 2)
  (format stream "  movl %eax, ~a(%esp)~%" (- si 12))   ; and save the object

  (emit-expr stream obj (- si 12)  env)                 ; calculate object pointer
  (format stream "  movl ~a(%esp), %ecx~%" (- si 12))
  (format stream "  movl ~a(%esp), %ebx~%" (- si 4))
  (format stream "  movl %eax, (%ecx,%ebx)~%")          ; store object in the vector 
  
  (format stream "  movl ~a(%esp), %eax~%" (- si 8)))  ; return the vector object (this simplifies processing
					               ; vector constructor expressions (vector v1 v2 v3 ...)

  
(defun emit-begin (stream expr-list si env)
  (dolist (x (butlast expr-list))
    (emit-expr stream x si env))

  (if *tail-context* (setq *tail-expression* t))

  (emit-expr stream (car (last expr-list)) si env)

  (setq *tail-expression* nil))

(defun emit-make-string (stream size si env)
  (emit-expr stream size si env)
  (format stream "  movl %eax, 0(%esi)~%")
  (format stream "  movl %eax, %ebx~%")
  (format stream "  sarl $2, %ebx~%") ; since strings don't need one whole word to store a character;
  (format stream "  orl $1, %ebx~%")  ; one byte is sufficient; space required is therefore (ceiling (/ size 4))
  (format stream "  movl %esi, %eax~%")
  (format stream "  orl $3, %eax~%")
  (format stream "  addl $11, %ebx~%")
  (format stream "  andl $-8, %ebx~%")
  (format stream "  addl %ebx, %esi~%"))

(defun emit-string-ref (stream string-obj index si env)
  (emit-expr stream index si env)
  (format stream "  movl %eax, %ebx~%")
  (format stream "  sarl $2, %ebx~%") ; same reason as above; to identify the byte in the word to pick
  (emit-expr stream string-obj si env)
  (format stream "  subl $-3, %eax~%")
  (format stream "  addl $4, %ebx~%")
  (format stream "  movl (%eax,%ebx), %eax~%"))

(defun emit-string-set! (stream string-obj index char si env)
  (emit-expr stream index si env)
  (format stream "  movl %eax, ~a(%esp)~%" (- si 4))
  (format stream "  sarl $2, ~a(%esp)~%" (- si 4)) ; same reason as above; to identify the byte in the word to pick
  (format stream "  addl $4, ~a(%esp)~%" (- si 4))

  (emit-expr stream string-obj (- si 4) env)
  (format stream "  movl %eax, ~a(%esp)~%" (- si 8))
  (format stream "  subl $-3, %eax~%")
  (format stream "  movl %eax, ~a(%esp)~%" (- si 12))

  (emit-expr stream char (- si 12) env)
  (format stream "  movl ~a(%esp), %ecx~%" (- si 12))
  (format stream "  movl ~a(%esp), %ebx~%" (- si 4))
  (format stream "  movl %eax, (%ecx,%ebx)~%")

  (format stream "  movl ~a(%esp), %eax~%" (- si 8)))

(defun emit-labels (stream lvar-list expr si env)
  (let ((new-env env))
    (dolist (lvar-item lvar-list)
      (let ((label (first lvar-item)))
	(progn (setq new-env (extend-env (symbol-name (first lvar-item)) (cons 'param label) new-env))
	       (emit-code label (second (second lvar-item)) 
			  (third (second lvar-item)) (fourth (second lvar-item)) si new-env))))

    (if (not *entry-label-emitted*)
	(progn (format stream "_lisp_entry:~%")
	       (setq *entry-label-emitted* t)))
    
    (emit-expr stream expr si new-env)))

(defun emit-labelcall (stream label-name arg-list si env)
  (let ((val (- si 4))) ;skip one word for the return point
    (dolist (arg arg-list)
      (progn (emit-expr stream arg val env)
	     (format stream "  movl %eax, ~a(%esp)~%" val)
	     (incf val -4)))
    (format stream "  addl $~a, %esp~%" (+ si 4)) ;set the stack pointer to one word below the return point
    (format stream "  call ~a~%" (cdr (lookup label-name env)))
    (format stream "  subl $~a, %esp~%" (+ si 4))))

(defun emit-closure (stream label-name var-list si env)
  (format stream "  movl $~a, 0(%esi)~%" (cdr (cdr (lookup label-name env)))) ; store label in 0(%esi)

  (let ((i 0))

    (dolist (var var-list)
      (emit-expr stream var si env)
      (format stream "  movl %eax, ~a(%esi)~%" (incf i 4))) ;push evaluated values onto %esi

    (format stream "  movl %esi, %eax~%") ;;tag for closure objects is 6
    (format stream "  orl $6, %eax~%")

    (format stream "  movl $~a, %ebx~%" (length var-list)) ;adjust %esi so that it is aligned with a double word address
    (format stream "  addl $11, %ebx~%")
    (format stream "  andl $-8, %ebx~%")
    (format stream "  addl %ebx, %esi~%")))

(defun emit-code (label param-list free-var-list expr si env)
  (let ((stream (if *functions-stream*
		    *functions-stream*
		    (setq *functions-stream* (open "lisp_functions.s" :direction :output :if-exists :supersede)))))

    (format stream "~a:~%" label)
    (let ((val1 si) (val2 4) (new-env env))

      (dolist (param param-list)
	(progn (setq new-env (extend-env (symbol-name param) (cons 'param val1) new-env))
	       (incf val1 -4)))

      (dolist (free-var free-var-list)
	(progn (setq new-env (extend-env (symbol-name free-var) (cons 'free-var val2) new-env))
	       (incf val2 4)))

      (emit-expr stream expr val1 new-env)
      (format stream "  ret~%"))))

(defun emit-funcall-no-tail-call (stream oper-expr arg-list si env)
  (let ((val (- si 8))) ;skip two words, one for the return point, one for the current closure pointer (%edi)

    (format stream "  movl %edi, ~a(%esp)~%" si)          ; save current closure pointer (%edi)

    (dolist (arg arg-list)                                ; evaluate the arguments and push them onto the stack
      (progn (emit-expr stream arg val env)
	     (format stream "  movl %eax, ~a(%esp)~%" val)
	     (incf val -4)))

    (emit-expr stream oper-expr si env)                   ; evaluate the operator and extract address of closure object
    (format stream "  subl $6, %eax~%")                   ; (by subtracting 6 from it)
    (format stream "  movl %eax, %edi~%")                 ; store the closure object's address in edi

    (format stream "  addl $~a, %esp~%" si)               ; set the stack pointer to one word below the return point
    (format stream "  call *(%eax)~%")                    ; call the function stored at this address
    (format stream "  subl $~a, %esp~%" si)               ; restore esp

    (format stream "  movl ~a(%esp), %edi~%" si)))        ; restore edi

(defun emit-funcall-with-tail-call (stream oper-expr arg-list si env)
  (let ((val si))

    (dolist (arg arg-list)                                ; evaluate the arguments and push them onto the stack
      (progn (emit-expr stream arg val env)
	     (format stream "  movl %eax, ~a(%esp)~%" val)
	     (incf val -4)))

    (emit-expr stream oper-expr val env)                  ; evaluate the operator and extract the closure pointer
    (format stream "  subl $6, %eax~%")                   ; (by subtracting 6 from it)
    (format stream "  movl %eax, %edi~%")                 ; store the closure object's address in edi

    ;copy the arguments to positions adjacent to the unchanged return point
    (do ((i si (+ i -4))
	 (x -4 (+ x -4)))
	((< i (+ si (* -4 (length arg-list)))))
      (progn (format stream "  movl ~a(%esp), %eax~%" i)
	     (format stream "  movl %eax, ~a(%esp)~%" x)))

    (format stream "  jmp *(%edi)~%")))


(defun special-op-p (x)
  (or (equal x 'add1)
      (equal x 'sub1)
      (equal x 'integer->char)
      (equal x 'char->integer)
      (equal x 'zero?)
      (equal x 'null?)
      (equal x 'not)
      (equal x 'integer?)
      (equal x 'character?)
      (equal x 'boolean?)
      (equal x '+)
      (equal x '-)
      (equal x '*)
      (equal x '=)
      (equal x 'char=?)
      (equal x '<)
      (equal x '>)
      (equal x 'let)
      (equal x 'if)
      (equal x 'cons)
      (equal x 'car)
      (equal x 'cdr)
      (equal x 'make-vector)
      (equal x 'vector-ref)
      (equal x 'vector-set!)
      (equal x 'begin)
      (equal x 'make-string)
      (equal x 'string-ref)
      (equal x 'string-set!)
      (equal x 'labels)
      (equal x 'labelcall)
      (equal x 'funcall)
      (equal x 'lambda)
))

(defun extract-free-vars (var-list expr)
  (cond ((and (atom expr)
	      (not (equal expr 't))
	      (not (null expr))
	      (variable-p expr)
	      (not (special-op-p expr))
	      (not (member expr var-list)))
	 (list expr))
	((listp expr)
	 (cond ((equal (first expr) 'let)
		(let ((free-vars-in-init-forms) (free-vars-in-body))
		  (progn
		    (setq free-vars-in-init-forms (mapcan (curry #'extract-free-vars var-list) 
							  (mapcan #'last (second expr))))
		    (setq free-vars-in-body (extract-free-vars  (concatenate 'list
									     (mapcar #'car (second expr))
									     var-list)
								(third expr)))
		    (remove-duplicates (concatenate 'list 
						    free-vars-in-init-forms
						    free-vars-in-body)))))
	       ((equal (first expr) 'lambda)
		(remove-duplicates (extract-free-vars (concatenate 'list
								   (second expr)
								   var-list)
						      (third expr))))
	       (t (remove-duplicates (mapcan (curry #'extract-free-vars var-list) expr)))))))

(defun convert-lambdas (expr)
  (cond ((atom expr) expr)
	((equal (first expr) 'lambda) (list 'lambda 
					    (second expr) 
					    (extract-free-vars (second expr) (third expr)) 
					    (convert-lambdas (third expr))))
	(t (cons (convert-lambdas (car expr)) (convert-lambdas (cdr expr))))))

(defun build-closures (expr)

  (let ((labels-list) 
	(result-expr))

    (defun build-closures-internal (expr)
      (cond ((atom expr) expr)
	    ((equal (first expr) 'lambda)
	     (let* ((label (gensym))
		    (code (list label (concatenate 'list (list 'code) (build-closures-internal (cdr expr))))))
	       (progn (setq labels-list (append labels-list (list code)))
		      (concatenate 'list (list 'closure) (list label) (third expr)))))
	    (t (cons (build-closures-internal (car expr)) (build-closures-internal (cdr expr))))))

    (setq result-expr (build-closures-internal expr))

    (nconc (list 'labels) (list labels-list) (list result-expr))))

(defun convert-quote (expr)
  (if (immediate-exp-p expr)  expr
      (convert-list-expr-internal expr)))

(defun convert-complex-constants (expr)

  (let ((let-list) 
	(result-expr)
	(complex-constants-map (make-hash-table :test 'equal)))

    (defun convert-complex-constants-internal (expr)
      (cond ((and (atom expr) (not (simple-vector-p expr)) (not (stringp expr))) expr)
	    ((or (simple-vector-p expr) (stringp expr) (equal (first expr) 'quote))
	     (let* ((key (if (or (simple-vector-p expr) (stringp expr)) expr (second expr)))
		    (val (gethash key complex-constants-map)))
	       (if val
		   val
		   (let ((label (gensym)))
		     (setf (gethash key complex-constants-map) label)
		     (setq let-list (append let-list (list (list label (convert-constant key)))))
		     label))))
	    ((listp expr) (cons (convert-complex-constants-internal (car expr)) 
				(convert-complex-constants-internal (cdr expr))))))

    (setq result-expr (convert-complex-constants-internal expr))

    (nconc (list 'let) (list let-list) (list result-expr))))

;to convert (list 1 2 3) to (cons 1 (cons 2 (cons 3 nil)))
(defun convert-list-expressions (expr)
  (cond ((atom expr) expr)
	((equal (first expr) 'list) (convert-list-expr-internal (cdr expr)))
	(t (cons (convert-list-expressions (car expr)) (convert-list-expressions (cdr expr))))))

;internal function used by convert-list-expressions
(defun convert-list-expr-internal (expr)
  (cond ((atom expr) expr)
	((null (cdr expr))
#|
	 (list 'cons (convert-list-expr-internal (car expr)) nil))
	(t (list 'cons (convert-list-expr-internal (car expr)) (convert-list-expr-internal (cdr expr))))))
|#
	 (list 'cons (car expr) nil))
	(t (list 'cons (car expr) (convert-list-expr-internal (cdr expr))))))



(defun constant-atom-p (expr)
  (and (atom expr)
       (or (immediate-exp-p expr) (stringp expr))))

;checks whether an expression is a constant or not
(defun constant-p (expr)
  (cond ((simple-vector-p expr)
	 (if (equal (length expr) 0)
	     t
	     (and (constant-p (aref expr 0)) (constant-p (subseq expr 1 (length expr))))))
	((atom expr)
	 (constant-atom-p expr))
	((listp expr)
	 (and (constant-p (car expr)) (constant-p (cdr expr))))
	(t (error "Only atoms, lists and vectors handled"))))

(defun convert-vector-to-list (v)
  (loop for i from 0 to (1- (length v))
       collecting (aref v i)))

(defun convert-constant (expr)
  (if (not (constant-p expr))
      (error "convert-constant: not a constant expression (~a)" expr)
      (cond ((simple-vector-p expr)
	     (concatenate 'list (list  'vector) (convert-vector-to-list expr)))
	    ((stringp expr)
	     (list 'string expr))
	    ((atom expr) expr)
	    ((listp expr) (convert-list-expr-internal expr)))))

;convert (vector v1 v2 v3 ...) to (vector-set! (vector-set! (vector-set! (make-vector <n>) 0 v1) 1 v2) 2 v3)
(defun convert-vector-expressions (expr)
  (cond ((atom expr) expr)
	((equal (first expr) 'vector) (convert-vector-expr-internal1 (cdr expr) (length (cdr expr))))
	(t (cons (convert-vector-expressions (car expr)) (convert-vector-expressions (cdr expr))))))

(defun convert-vector-expr-internal1 (expr n)
  (let ((index (1- n)))
    (defun convert-vector-expr-internal2 (expr)
      (cond ((null (cdr expr)) 
	     (prog1 (list 'vector-set! (list 'make-vector n) index (car expr)) (decf index)))
	    (t 
	     (prog1 (list 'vector-set! (convert-vector-expr-internal2 (cdr expr)) index (car expr))
		 (decf index)))))

    (convert-vector-expr-internal2 expr)))

;convert (string "abc") to (string-set! (string-set! (string-set! (make-vector 3) 2 #\c) 1 #\b) 0 #\a)
(defun convert-string-expressions (expr)
  (cond ((atom expr) expr)
	((equal (first expr) 'string) (convert-string-expr-internal (second expr)))
	(t (cons (convert-string-expressions (car expr)) (convert-string-expressions (cdr expr))))))

(defun convert-string-expr-internal (expr)
  (let ((n (1- (length expr)))
	(result))
    (dotimes (i n)
      (if (null result)
	  (setq result (list 'string-set! (list 'make-string (length expr)) n (char expr n)))
	  (setq result (list 'string-set! result (- n i) (char expr (- n i))))))
    (list 'string-set! result 0 (char expr 0))))

;list of all variables in a lambda or let expression
(defun get-var-list (expr)
  (cond ((equal (first expr) 'lambda) (second expr))
	((equal (first expr) 'let) (mapcar #'car (second expr)))
	(t (error "get-var-list: argument should be a lambda or a let"))))

;returns list of all the variables
;in var-list that are set in expr
(defun vars-set-in-expr (var-list expr)
  (let ((result))
    (dolist (var var-list)
      (if (not (no-assignments-to-var-p expr var))
	  (setq result (nconc result (list var)))))
    result))

;check if any of the variables in the list are assigned to in the given expression
(defun vars-set-in-expr-p (var-list expr)
  (if (null var-list)
      nil
      (or (not (no-assignments-to-var-p expr (car var-list)))
	  (vars-set-in-expr-p (cdr var-list) expr))))
 
;check whether there are any assignments in the given expression
(defun no-assignments-p (expr)
  (cond ((atom expr) t)
	((equal (first expr) 'set!) nil)
	(t (and (no-assignments-p (car expr)) 
		(no-assignments-p (cdr expr))))))

;check if there are any assignments to a given variable in the expression
(defun no-assignments-to-var-p (expr var-name)
  (if (no-assignments-p expr) t
      (cond ((atom expr) t)
	    ((and (equal (first expr) 'set!) (not (equal (second expr) var-name))) t)
	    ((and (equal (first expr) 'set!) (equal (second expr) var-name)) nil)
	    (t (and (no-assignments-to-var-p (car expr) var-name) 
		    (no-assignments-to-var-p (cdr expr) var-name))))))

;identify assigned variables that are not
;redefined in the inner lambdas/lets
;that contain the assignment
(defun non-redefined-vars-old (var-list expr)
  (let ((before-assignment t) ;todo: incorrect; need to check that the lambda/let doesn't contain the 'set!'
	(result (copy-list var-list)))
    (defun non-redefined-vars-old-internal (expr)
       (cond ((listp expr)
	      (cond ((equal (first expr) 'set!) 
		     (setq before-assignment nil))
		    ((and before-assignment
			 (or (equal (first expr) 'lambda)
			     (equal (first expr) 'let)))
		     (setq result (remove-if (lambda (x) (member x (get-var-list expr))) result)))
		    (t (progn (non-redefined-vars-old-internal (car expr))
			      (non-redefined-vars-old-internal (cdr expr))))))))
    (non-redefined-vars-internal expr)
    result))

;identify assigned variables that are not
;redefined in the inner lambdas/lets
;that contain the assignment
(defun non-redefined-vars (var-list expr)
  (let ((result (copy-list var-list))
	(curr-var-list))
    (defun non-redefined-vars-internal (expr)
      (if (and (listp expr) (not (null expr)))
	  (cond ((or (equal (first expr) 'lambda)
		     (equal (first expr) 'let))
		 (progn 
		   (setq curr-var-list (if (equal (first expr) 'lambda) 
					   (second expr)
					   (mapcar (lambda (x) (first x)) (second expr))))
		   (non-redefined-vars-internal (third expr))
		   (setq curr-var-list nil)))
		((and (equal (first expr) 'set!)
		      (member (second expr) curr-var-list)
		      (member (second expr) var-list))
		 (progn (setq result (remove (second expr) result))
			(non-redefined-vars-internal (third expr))))
		(t (progn (non-redefined-vars-internal (car expr))
			  (non-redefined-vars-internal (cdr expr)))))))
    (non-redefined-vars-internal expr)
    result))

;replace list of variable declarations with
;new symbols passed in the map
(defun replace-declarations (var-list orig-list replacement-map type)
  (cond ((equal type 'lambda)
	 (mapcar (lambda (x) (if (member x var-list) (gethash x replacement-map) x)) orig-list))
	((equal type 'let)
	 (mapcar (lambda (x) (list (if (member (first x) var-list) 
				       (gethash (first x) replacement-map)
				       (first x))
				   (second x))) orig-list))
	(t (error "replace-declarations: type should be 'lambda' or 'let"))))

;replaces (set! <var> <value>) with (vector-set! <tempvar> 0 <value>)
;and other references to <var> with <tempvar>
(defun replace-references (var-list expr replacement-map)
  (cond ((member expr var-list) (list 'vector-ref expr 0))
	((atom expr) expr)
	((and (equal (first expr) 'set!)
	      (member (second expr) var-list))
	 (list 'vector-set! (second expr) 0 (third expr)))
	(t (cons (replace-references var-list (car expr) replacement-map)
		 (replace-references var-list (cdr expr) replacement-map)))))

;convert (set! ...)  with (vector-set! ...)
(defun convert-assignments (expr)
  (cond ((atom expr) expr)
	((or (equal (first expr) 'lambda)
	     (equal (first expr) 'let))    
	 (if (or (null (second expr))
		 (not (vars-set-in-expr-p (get-var-list expr) (third expr))))
	     (list (first expr) 
		   (if (equal (first expr) 'lambda) 
		       (second expr)
		       (mapcar (lambda (x) (list (first x) (convert-assignments (second x)))) (second expr)))
		   (convert-assignments (third expr)))
	     ;split the var list into a) assigned vars that are not redefined in
	     ;in the inner lambdas/lets containing the assignment and b) remaining
	     ;variables.  
	     (let* ((assigned-vars (non-redefined-vars (vars-set-in-expr (get-var-list expr) (third expr)) 
						       (third expr)))
		    (remaining-vars (if (equal (first expr) 'lambda)
					(remove-if (lambda (v) (member v assigned-vars)) (get-var-list expr))
					(remove-if (lambda (v) (member (first v) assigned-vars))
						   (second expr))))
		    (map (make-hash-table :test 'equal)))
	       (dolist (v assigned-vars)
		 (setf (gethash v map) (gensym)))
	       (list (first expr)
		     (concatenate 'list 
				  (replace-declarations assigned-vars (second expr) map (first expr))
				  remaining-vars)
		     (list 'let 
			   (mapcar (lambda (x) (list x (list 'vector (gethash x map)))) assigned-vars)
			   (convert-assignments (replace-references assigned-vars (third expr) map))))
	       )))
	(t (cons (convert-assignments (car expr)) (convert-assignments (cdr expr))))))