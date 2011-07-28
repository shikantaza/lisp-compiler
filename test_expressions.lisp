(defparameter *test-expressions* nil)

(defmacro add-expr (expr)
  `(setq *test-expressions* (nconc *test-expressions* (list ,expr))))

(add-expr '(let ((mult (lambda (x y) (* x y)))
		 (add (lambda (x y) (+ x y)))
		 (f (lambda (x y) (+ (mult x y) (add x y)))))
	    (f 10 19)))

(add-expr '(let ((f (lambda () (car (quote (1 2 3 4)))))) (f)))

(add-expr '(let ((f (lambda () (car (list 1 2 3 4))))) (f)))

(add-expr '(car (quote (1 . 2))))

(add-expr '(let ((f (lambda () (quote (1 . 2)))))
	    (= (f) (f))))
      
(add-expr '(let ((f (lambda () (quote (1 . 2))))
		 (g (lambda () (quote (1 . 2)))))
	    (= (f) (g))))

(add-expr '(let ((f (lambda () (vector-ref #(1 2 3 4) 3)))) (f)))

(add-expr '((cdr (cons (lambda (x) (* x x)) (lambda (x) (+ x x)))) 10))

(add-expr '(let ((f (cons (lambda (x) (* x x)) (lambda (x) (+ x x))))) ((car f) 10)))

(add-expr '(let ((f (lambda (c)
		      (cons (lambda (v) (set! c v))
			    (lambda () c)))))
	    (let ((p (f 0)))
	      (begin ((car p) 12)
		     ((cdr p))))))

(defun run-test (n)
  (cle (nth n *test-expressions*)))
