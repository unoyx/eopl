#lang eopl

(require racket/trace)

(define empty-env
  empty)

(define extend-env
  (lambda (saved-var saved-val saved-env)
    (append saved-env (list (list saved-var saved-val)))))

(define apply-env
  (lambda (env search-var)
    (cadr (assoc search-var env))))

(define empty-env?
  (lambda (env)
    (= (length env) 0)))

(define show-env
  (lambda (env)
    (if (= (length env) 0)
        (eopl:printf "end\n")
        (begin (eopl:printf "~, " (car env))
               (show-env (cdr env))))))

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?)))

(define (report-expval-extractor-error arg val)
  (eopl:error 'extracte-data "arg is: ~s, val is: ~s" arg val))

(define expval->num
  (lambda (val)
    (cases expval val
           (num-val (num) num)
           (else (report-expval-extractor-error 'num val)))))

(define expval->bool
  (lambda (val)
    (cases expval val
           (bool-val (bool) bool)
           (else (report-expval-extractor-error 'bool val)))))

(define init-env
  (lambda ()
    empty-env))

(define value-of-program
  (lambda (pgm env)
    (cases program pgm
           (a-program (exp1)
                      (value-of exp1 env)))))
(define value-of
  (lambda (exp env)
    (cases expression exp
           (const-exp (num) (num-val num))
           (var-exp (var) (apply-env env var))
           (diff-exp (exp1 exp2)
                     (let ((val1 (value-of exp1 env))
                           (val2 (value-of exp2 env)))
                       (let ((num1 (expval->num val1))
                             (num2 (expval->num val2)))
                         (num-val
                          (- num1 num2)))))
           (zero?-exp (exp1)
                      (let ((val1 (value-of exp1 env)))
                        (let ((num1 (expval->num val1)))
                          (if (zero? num1)
                              (bool-val #t)
                              (bool-val #f)))))
           (if-exp (exp1 exp2 exp3)
                   (let ((val1 (value-of exp1 env)))
                     (if (expval->bool val1)
                         (value-of exp2 env)
                         (value-of exp3 env))))
           (let-exp (var exp1 body)
                    (let [(val1 (value-of exp1 env))]
                      (value-of body
                                (extend-env var val1 env)))))))

(define scanner-let
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)))

(define grammar-let
  '((program
     (expression)
     a-program)
    (expression
     (number)
     const-exp)
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)
    (expression
     ("zero?" "(" expression ")")
     zero?-exp)
    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)
    (expression
     (identifier)
     var-exp)
    (expression
     ("let" identifier "=" expression "in" expression)
     let-exp)))

(sllgen:make-define-datatypes scanner-let grammar-let)

(define list-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes scanner-let grammar-let)))

;; (eopl:pretty-print (list-the-datatypes) (current-output-port))

(define just-scan
  (sllgen:make-string-scanner scanner-let grammar-let))
(define scan&parse
  (sllgen:make-string-parser scanner-let grammar-let))

(define test-driver
  (lambda (case)
    (letrec [(env empty-env)
             (res (value-of-program (scan&parse case) env))]
      (eopl:printf "case: ~a, result: ~a, env: ~a\n" case res env))))

(test-driver "3")

(test-driver "-(2, 3)")

(test-driver "zero? (2)")

(test-driver "zero? (0)")

(test-driver "if zero? (0) then 1 else 2")

(test-driver "let a = 10 in -(a, 9)")
