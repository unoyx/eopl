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

;; 表示expression的可能返回值类型
(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (list-val
   (my-list (lambda (x)
              (or pair? null?)))))

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

(define expval->list
  (lambda (val)
    (cases expval val
           (list-val (my-list) my-list)
           (else (report-expval-extractor-error 'list val)))))

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
           (empty-list-exp () (list-val empty))
           (null?-exp (exp) (bool-val (null? (expval->list (value-of exp env)))))
           (const-exp (num) (num-val num))
           (var-exp (var) (apply-env env var))
           (minus-exp (exp) (num-val (- (expval->num (value-of exp env)))))
           (car-exp (exp) (car (expval->list (value-of exp env))))
           (cdr-exp (exp) (cdr (expval->list (value-of exp env))))
           (create-list-exp (exp) (letrec [(exp-res (map (lambda (e)
                                                           (value-of e env)) exp))
                                           ;; 遍历一个列表，将每个元素包裹在list-val中
                                           (list-val-iter (lambda (the-list)
                                                            (if (null? the-list)
                                                                (list-val empty)
                                                                (list-val (cons (car the-list)
                                                                                (list-val-iter (cdr the-list)))))))]
                                    (list-val-iter exp-res)))
           (cons-exp (exp1 exp2)
                     (let ((val1 (value-of exp1 env))
                           (val2 (value-of exp2 env)))
                       ;; cons操作可以处理所有expval，所以这里没有取value的操作
                       (list-val
                        (cons val1 val2))))
           (diff-exp (exp1 exp2)
                     (let ((val1 (value-of exp1 env))
                           (val2 (value-of exp2 env)))
                       (let ((num1 (expval->num val1))
                             (num2 (expval->num val2)))
                         (num-val
                          (- num1 num2)))))
           (add-exp (exp1 exp2)
                    (let ((val1 (value-of exp1 env))
                          (val2 (value-of exp2 env)))
                      (let ((num1 (expval->num val1))
                            (num2 (expval->num val2)))
                        (num-val
                         (+ num1 num2)))))
           (equal?-exp (exp1 exp2)
                       (let ((val1 (value-of exp1 env))
                             (val2 (value-of exp2 env)))
                         (let ((num1 (expval->num val1))
                               (num2 (expval->num val2)))
                           (bool-val
                            (= num1 num2)))))
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
     ("list" "(" (separated-list expression ",") ")")
     create-list-exp)
    (expression
     ("emptylist")
     empty-list-exp)
    (expression
     ("null?" "(" expression ")")
     null?-exp)
    (expression
     ("car" "(" expression ")")
     car-exp)
    (expression
     ("cdr" "(" expression ")")
     cdr-exp)
    (expression
     ("cons" "(" expression "," expression ")")
     cons-exp)
    (expression
     ("minus" "(" expression ")")
     minus-exp)
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)
    (expression
     ("+" "(" expression "," expression ")")
     add-exp)
    (expression
     ("zero?" "(" expression ")")
     zero?-exp)
    (expression
     ("equal?" "(" expression "," expression ")")
     equal?-exp)
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

;; test cases

(define test-driver
  (lambda (case)
    (letrec [(env empty-env)
             (res (value-of-program (scan&parse case) env))]
      (eopl:printf "case: ~a, result: ~a\n" case res))))

(test-driver "3")
(test-driver "-(2, 3)")
(test-driver "zero? (2)")
(test-driver "zero? (0)")
(test-driver "if zero? (0) then 1 else 2")
(test-driver "let a = 10 in -(a, 9)")
(test-driver "minus(-(minus(5),9))")
(test-driver "equal?(+(2, minus(3)), minus(1))")
(test-driver "null? (emptylist)")
(test-driver "cons (2, emptylist)")
(test-driver "+(car(cons(2, emptylist)), 1)")
(test-driver "let x = 4 in cons(x,cons(cons(-(x,1),emptylist),emptylist))")
(test-driver "list(1, 2, 3)")
(test-driver "equal?(+(car(list(1, 2, 3)),4),5)")
