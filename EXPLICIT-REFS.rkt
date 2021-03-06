#lang eopl
(require rackunit)
(require "base.rkt")

;; expression type
(define (local-pair? val)
  (or (null? val) (pair? val)))

(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (pair-val (pair local-pair?))
  (proc-val (proc procedure?))
  (ref-val (ref reference?))
  )

(define (expval->num val)
  (cases expval val
    (num-val (num) num)
    (else (report-expval-extractor-error 'num val))))

(define (expval->bool val)
  (cases expval val
    (bool-val (bool) bool)
    (else (report-expval-extractor-error 'bool val))))

(define (expval->pair val)
  (cases expval val
    (pair-val (pair) pair)
    (else (report-expval-extractor-error 'pair val))))

(define (expval->proc val)
  (cases expval val
    (proc-val (proc) proc)
    (else (report-expval-extractor-error 'proc val))))

(define (expval->ref val)
  (cases expval val
    (ref-val (ref) ref)
    (else (report-expval-extractor-error 'ref val))))

;; envirionment
(define (init-env)
  (extend-env 'false (bool-val #f)
              (extend-env 'true (bool-val #t)
                          (empty-env))))

;; store
(define (empty-store)
  '())

(define the-store 'uninitialized)

(define (get-store)
  the-store)

(define (initialize-store)
  (set! the-store (empty-store)))

(initialize-store)

(define (reference? v)
  (integer? v))

(define (newref val)
  (let ((next-ref (length the-store)))
    (set! the-store (append the-store (list val)))
    next-ref))

(define (deref ref)
  (list-ref the-store ref))

(define (setref! ref val)
  (set! the-store
        (letrec
            ((setref-inner
              (lambda (store1 ref1)
                (cond
                  ((null? store1)
                   (report-invalid-reference ref the-store))
                  ((zero? ref1)
                   (cons val (cdr store1)))
                  (else
                   (cons
                    (car store1)
                    (setref-inner
                     (cdr store1) (- ref1 1))))))))
          (setref-inner the-store ref))))

(define-datatype program program?
  (a-program (exp expression?)))

;; ENHANCE 3.22
;; It can make parser&value-of more clean, but will increase evaluate time,
;; consider about how to measure this.
(define grammar-let
  '(;; (program (expression) a-progam)
    (expression (number) const-exp)
    (expression (identifier) var-exp)
    (expression ("zero?" expression) zero?-exp)
    (expression ("equal?" expression "," expression) eq?-exp)
    (expression ("greater?" expression "," expression) gt?-exp)
    (expression ("less?" expression "," expression) ls?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    (expression ("let*" (arbno identifier "=" expression) "in" expression) let-star-exp)
    (expression ("minus" "(" expression ")") minus-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("+" "(" expression "," expression ")") add-exp)
    (expression ("*" "(" expression "," expression ")") mul-exp)
    (expression ("/" "(" expression "," expression ")") div-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("car" expression) car-exp)
    (expression ("cdr" expression) cdr-exp)
    (expression ("null?" expression) null?-exp)
    (expression ("list" "(" (separated-list expression ",") ")") list-exp)
    (expression ("cond" (arbno expression "==>" expression) "end") cond-exp)
    (expression ("unpack" (arbno identifier) "=" expression "in" expression) unpack-exp)
    (expression ("proc" "(" (separated-list identifier ",")")" expression) proc-exp)
    (expression ("letrec" (arbno identifier "(" (separated-list identifier ",") ")" "=" expression) "in" expression) letrec-exp)
    (expression ("(" expression (arbno expression)")") call-exp)
    (expression ("newref" "(" expression ")") newref-exp)
    (expression ("deref" "(" expression ")") deref-exp)
    (expression ("setref" "(" expression "," expression ")") setref-exp)
    (expression ("begin" (separated-list expression ";" ) "end") begin-exp)
    ))

(sllgen:make-define-datatypes scanner-spec-a grammar-let)

(define scan&parse
  (sllgen:make-string-parser scanner-spec-a grammar-let))

(define (value-of-exp e)
  (value-of (scan&parse e)
            (init-env)))

(define (binds-vars vars vals env)
  (if (null? vars)
      (if (null? (expval->pair vals))
          env
          (eopl:error "identifier mismatch with list length"))
      (binds-vars (cdr vars) (cdr (expval->pair vals))
                  (extend-env (car vars) (car (expval->pair vals)) env))))

(define (extends-env vars exps env)
  (if (null? vars)
      env
      (extends-env (cdr vars) (cdr exps)
                   (extend-env (car vars)
                               (value-of (car exps) env)
                               env))))

(define (value-of exp env)
  (cases expression exp
    (const-exp (num) (num-val num))
    (var-exp (var) (apply-env env var))
    (diff-exp (exp1 exp2)
              (let ((val1 (value-of exp1 env))
                    (val2 (value-of exp2 env)))
                (let ((num1 (expval->num val1))
                      (num2 (expval->num val2)))
                  (num-val (- num1 num2)))))
    (zero?-exp (exp1)
               (let ((val1 (value-of exp1 env)))
                 (let ((num1 (expval->num val1)))
                   (if (zero? num1)
                       (bool-val #t)
                       (bool-val #f)))))
    (eq?-exp (exp0 exp1)
             (let ((val0 (value-of exp0 env))
                   (val1 (value-of exp1 env)))
               (let ((num0 (expval->num val0))
                     (num1 (expval->num val1)))
                 (if (= num0 num1)
                     (bool-val #t)
                     (bool-val #f)))))
    (gt?-exp (exp0 exp1)
             (let ((val0 (value-of exp0 env))
                   (val1 (value-of exp1 env)))
               (let ((num0 (expval->num val0))
                     (num1 (expval->num val1)))
                 (if (> num0 num1)
                     (bool-val #t)
                     (bool-val #f)))))
    (ls?-exp (exp0 exp1)
             (let ((val0 (value-of exp0 env))
                   (val1 (value-of exp1 env)))
               (let ((num0 (expval->num val0))
                     (num1 (expval->num val1)))
                 (if (< num0 num1)
                     (bool-val #t)
                     (bool-val #f)))))
    (if-exp (exp1 exp2 exp3)
            (let ((val1 (value-of exp1 env)))
              (if (expval->bool val1)
                  (value-of exp2 env)
                  (value-of exp3 env))))
    (let-exp (vars exps body)
             (letrec ((vals (map (lambda (exp)
                                   (value-of exp env)) exps))
                      (extends-env (lambda (vars vals env)
                                     (if (null? vars)
                                         env
                                         (extends-env (cdr vars) (cdr vals)
                                                      (extend-env (car vars) (car vals) env))))))
               (value-of body
                         (extends-env vars vals env))))
    (let-star-exp (vars exps body)
                  (value-of body
                            (extends-env vars exps env)))
    (minus-exp (exp0)
               (let ((val0 (value-of exp0 env)))
                 (num-val (- (expval->num val0)))))
    (add-exp (exp0 exp1)
             (let ((val0 (value-of exp0 env))
                   (val1 (value-of exp1 env)))
               (let ((num0 (expval->num val0))
                     (num1 (expval->num val1)))
                 (num-val (+ num0 num1)))))
    (mul-exp (exp0 exp1)
             (let ((val0 (value-of exp0 env))
                   (val1 (value-of exp1 env)))
               (let ((num0 (expval->num val0))
                     (num1 (expval->num val1)))
                 (num-val (* num0 num1)))))
    (div-exp (exp0 exp1)
             (let ((val0 (value-of exp0 env))
                   (val1 (value-of exp1 env)))
               (let ((num0 (expval->num val0))
                     (num1 (expval->num val1)))
                 (num-val (quotient num0 num1)))))
    (emptylist-exp ()
                   (pair-val '()))
    (cons-exp (exp0 exp1)
              (let ((val0 (value-of exp0 env))
                    (val1 (value-of exp1 env)))
                (pair-val (cons val0 val1))))
    (car-exp (exp0)
             (let ((val0 (expval->pair (value-of exp0 env))))
               (car val0)))
    (cdr-exp (exp0)
             (let ((val0 (expval->pair (value-of exp0 env))))
               (cdr val0)))
    (null?-exp (exp0)
               (let ((val0 (expval->pair (value-of exp0 env))))
                 (if (null? val0)
                     (bool-val #t)
                     (bool-val #f))))
    (list-exp (exps)
              (letrec ((vals (map (lambda (e)
                                    (value-of e env))
                                  exps))
                       (pack-pair-vals (lambda (list-vals)
                                         (if (null? list-vals)
                                             (pair-val '())
                                             (pair-val (cons (car list-vals)
                                                             (pack-pair-vals (cdr list-vals))))))))
                (pack-pair-vals vals)))
    (cond-exp (conds exps)
              (letrec ((cond-eval (lambda (conds exps)
                                    (if (expval->bool (value-of (car conds) env))
                                        (value-of (car exps) env)
                                        (cond-eval (cdr conds) (cdr exps))))))
                (cond-eval conds exps)))
    (unpack-exp (vars exp body)
                (letrec ((val (value-of exp env)))
                  (value-of body (binds-vars vars val env))))
    ;; ENHANCE 3.26
    ;; this may reduce the memory consume, consider about how to measure it.
    (proc-exp (vars body)
              (proc-val (lambda (vals)
                          (value-of body (extends-env vars vals env)))))
    (call-exp (rator rands)
              (let ((proc (expval->proc (value-of rator env))))
                (proc rands)))
    (letrec-exp (p-name-list b-vars-list p-body-list letrec-body)
                (letrec ((extend-env-rec (lambda (p-name b-vars p-body saved-env)
                                           (lambda (search-var)
                                             (if (eqv? search-var p-name)
                                                 (proc-val (lambda (vals)
                                                             (value-of p-body (extend-env-rec p-name b-vars p-body
                                                                                              (extends-env b-vars vals saved-env)))))
                                                 (apply-env saved-env search-var)))))
                         (extend-env-rec-helper (lambda (p-name-list b-vars-list p-body-list env)
                                                  (if (null? p-name-list)
                                                      env
                                                      (extend-env-rec-helper (cdr p-name-list) (cdr b-vars-list) (cdr p-body-list)
                                                                             (extend-env-rec (car p-name-list) (car b-vars-list) (car p-body-list) env))))))
                  (value-of letrec-body (extend-env-rec-helper p-name-list b-vars-list p-body-list env))))
    (newref-exp (exp1)
                (let ((v1 (value-of exp1 env)))
                  (ref-val (newref v1))))
    (deref-exp (exp1)
               (let* ((v1 (value-of exp1 env))
                      (ref1 (expval->ref v1)))
                 (deref ref1)))
    (setref-exp (exp1 exp2)
                (let* ((ref (expval->ref (value-of exp1 env)))
                       (v2 (value-of exp2 env)))
                  (begin (setref! ref v2)
                         (num-val 23))))
    (begin-exp (exps)
               (letrec ((value-seq (lambda (exps)
                                     (if (= (length exps) 1)
                                         (value-of (car exps) env)
                                         (begin (value-of (car exps) env)
                                                (value-seq (cdr exps)))))))
                 (value-seq exps)))
    ))

(check-equal? (value-of-exp "+ ( 1, 3 )")
              (num-val 4))
(check-equal? (value-of-exp "* ( + ( 1, 3 ), 2)")
              (num-val 8))
(check-equal? (value-of-exp "cond false ==> 0 true ==> 1 end")
              (num-val 1))
(check-equal? (value-of-exp "let x = 30
                             in let x = -(x,1)
                                    y = -(x,2)
                                in -(x,y)")
              (num-val 1))
(check-equal? (value-of-exp "let x = 30
                             in let* x = -(x,1)
                                     y = -(x,2)
                                in -(x,y)")
              (num-val 2))
(check-equal? (value-of-exp "car cons(1, emptylist)")
              (num-val 1))
(check-equal? (value-of-exp "null? emptylist")
              (bool-val #t))
(check-equal? (value-of-exp "car list (1, emptylist)")
              (num-val 1))
(check-equal? (value-of-exp "let u = 7
                             in unpack x y = cons(u, cons(3, emptylist))
                                in -(x, y)")
              (num-val 4))
(check-equal? (value-of-exp "let f = proc (x) proc (y) -(x, -(0, y))
                             in ((f 3) 4)")
              (num-val 7))
(check-equal? (value-of-exp "let f = proc (x, y) -(x, y)
                             in (f 3 4)")
              (num-val -1))
(check-equal? (value-of-exp "if zero? 0 then 1 else 2")
              (num-val 1))
(check-equal? (value-of-exp "letrec double(x)
                                    = if zero? x then 0 else + ((double -(x, 1)), 2)
                                    in (double 3)")
              (num-val 6))
(check-equal? (value-of-exp "letrec double(x)
                                    = if zero? x then 0 else + ((double -(x, 1)), 2)
                                    in (double 3)")
              (num-val 6))
(check-equal? (value-of-exp "let x = newref(newref(3))
                               in deref(deref(x))")
              (num-val 3))
(check-equal? (value-of-exp "let y = newref(newref(0))
                               in begin
                                 setref(deref(y), 11);
                                 deref(deref(y))
                               end")
              (num-val 11))
;; FIXME
;;(check-equal? (value-of-exp "letrec
;;                               even(x) = if zero? x then 1 else (odd -(x,1))
;;                               odd(x) = if zero? x then 0 else (even -(x,1))
;;                             in (odd 1)")
;;              (num-val 1))
(display "eof")