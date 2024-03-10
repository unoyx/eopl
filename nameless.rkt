#lang eopl
;; (require racket/trace)

(define empty-senv
  (lambda ()
    empty))

(define extend-senv
  (lambda (var senv)
    (cons var senv)))

(define extends-senv
  (lambda (vars senv)
    (if (null? vars)
        senv
        (extends-senv (cdr vars)
                      (cons (car vars)
                            senv)))))

(define apply-senv
  (lambda (senv var)
    (cond
      [(null? senv)
       (eopl:error 'binding "search value: ~s\n" var)]
      [(eqv? var (car senv))
       0]
      [else
       (+ 1 (apply-senv (cdr senv) var))])))

(define empty-env
  empty)

(define extend-env
  (lambda (saved-var saved-val saved-env)
    (append (list (list saved-var saved-val)) saved-env)))

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

(define environment?
  (lambda (env)
    (list? env)))

(define list-of-symbol?
  (lambda (symbols)
    (if (null? symbols)
        #t
        (and (symbol? (car symbols))
             (cdr symbols)))))

(define-datatype proc proc?
  (procedure
   (body expression?)
   (saved-env nameless-environment?)))

;; 表示expression的可能返回值类型
(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (list-val
   (my-list (lambda (x)
              (or pair? null?))))
  (proc-val
   (proc proc?)))

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

;; 作为对于表达式结果的类型检查
(define expval->proc
  (lambda (val)
    (cases expval val
      (proc-val (proc) proc)
      (else (report-expval-extractor-error 'proc val)))))

(define extend-env-iter
  (lambda (vars vals env)
    (if (null? vars)
        env
        (extend-env-iter (cdr vars)
                         (cdr vals)
                         (extend-env (car vars) (car vals) env)))))

(define translation-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (a-program
                  (translation-of exp1 (empty-senv)))))))

(define translation-of
  (lambda (exp senv)
    (cases expression exp
           (empty-list-exp () (empty-list-exp))
           (null?-exp (exp) (null?-exp (translation-of exp senv)))
           (const-exp (num) (const-exp num))
           (minus-exp (exp) (minus-exp (translation-of exp senv)))
           (car-exp (exp) (car-exp (translation-of exp senv)))
           (cdr-exp (exp) (cdr-exp (translation-of exp senv)))
           (create-list-exp (exps) (create-list-exp (map (lambda (exp)
                                                           (translation-of exp senv))
                                                         exps)))
           (cons-exp (exp1 exp2) (cons-exp (translation-of exp1 senv)
                                           (translation-of exp2 senv)))
           (add-exp (exp1 exp2) (add-exp (translation-of exp1 senv)
                                         (translation-of exp2 senv)))
           (equal?-exp (exp1 exp2) (equal?-exp (translation-of exp1 senv)
                                               (translation-of exp2 senv)))
           (diff-exp (exp1 exp2)
                     (diff-exp
                      (translation-of exp1 senv)
                      (translation-of exp2 senv)))
           (zero?-exp (exp1)
                      (zero?-exp
                       (translation-of exp1 senv)))
           (if-exp (exp1 exp2 exp3)
                   (if-exp
                    (translation-of exp1 senv)
                    (translation-of exp2 senv)
                    (translation-of exp3 senv)))
           (var-exp (var)
                    (nameless-var-exp (apply-senv senv var)))
           (let-exp (vars exps body)
                    (nameless-let-exp (map (lambda (exp1)
                                             (translation-of exp1 senv))
                                           exps)
                                      (translation-of body
                                                      (extends-senv vars senv))))
           (proc-exp (vars body)
                     (nameless-proc-exp (translation-of body
                                                        (extends-senv vars senv))))
           (call-exp (rator rands)
                     (call-exp (translation-of rator senv)
                               (map (lambda (rand)
                                      (translation-of rand senv))
                                    rands)))
           (else
            (eopl:error 'invalid-source-expression "exp: ~s\n" exp)))))

(define run
  (lambda (string)
    (value-of-program
     (translation-of-program
      (scan&parse string)))))

(define nameless-environment?
  (lambda (x)
    ((list-of expval?) x)))

(define empty-nameless-env
  (lambda ()
    '()))

(define extend-nameless-env
  (lambda (val nameless-env)
    (cons val nameless-env)))

(define extends-nameless-env
  (lambda (vals nameless-env)
    (if (null? vals)
        nameless-env
        (extends-nameless-env (cdr vals)
                              (cons (car vals) nameless-env)))))

(define apply-nameless-env
  (lambda (nameless-env n)
    (list-ref nameless-env n)))

(define apply-procedure
  (lambda (proc1 vals)
    (cases proc proc1
           (procedure (body saved-nameless-env)
                      (value-of body
                                (extends-nameless-env vals saved-nameless-env))))))

(define value-of
  (lambda (exp nameless-env)
    (cases expression exp
           (const-exp (num) (num-val num))
           (empty-list-exp () (list-val empty))
           (null?-exp (exp) (bool-val (null? (expval->list (value-of exp nameless-env)))))
           (minus-exp (exp) (num-val (- (expval->num (value-of exp nameless-env)))))
           (car-exp (exp) (car (expval->list (value-of exp nameless-env))))
           (cdr-exp (exp) (cdr (expval->list (value-of exp nameless-env))))
           (create-list-exp (exp) (letrec [(exp-res (map (lambda (e)
                                                           (value-of e nameless-env)) exp))
                                           ;; 遍历一个列表，将每个元素包裹在list-val中
                                           (list-val-iter (lambda (the-list)
                                                            (if (null? the-list)
                                                                (list-val empty)
                                                                (list-val (cons (car the-list)
                                                                                (list-val-iter (cdr the-list)))))))]
                                    (list-val-iter exp-res)))
           (cons-exp (exp1 exp2)
                     (let ((val1 (value-of exp1 nameless-env))
                           (val2 (value-of exp2 nameless-env)))
                       ;; cons操作可以处理所有expval，所以这里没有取value的操作
                       (list-val
                        (cons val1 val2))))
           (diff-exp (exp1 exp2)
                     (let ((val1 (value-of exp1 nameless-env))
                           (val2 (value-of exp2 nameless-env)))
                       (let ((num1 (expval->num val1))
                             (num2 (expval->num val2)))
                         (num-val
                          (- num1 num2)))))
           (add-exp (exp1 exp2)
                    (let [(val1 (value-of exp1 nameless-env))
                          (val2 (value-of exp2 nameless-env))]
                      (let [(num1 (expval->num val1))
                            (num2 (expval->num val2))]
                        (num-val
                         (+ num1 num2)))))
           (equal?-exp (exp1 exp2)
                       (let ((val1 (value-of exp1 nameless-env))
                             (val2 (value-of exp2 nameless-env)))
                         (let ((num1 (expval->num val1))
                               (num2 (expval->num val2)))
                           (bool-val
                            (= num1 num2)))))
           (zero?-exp (exp1)
                      (let ((val1 (value-of exp1 nameless-env)))
                        (let ((num1 (expval->num val1)))
                          (if (zero? num1)
                              (bool-val #t)
                              (bool-val #f)))))
           (if-exp (exp1 exp2 exp3)
                   (let ((val1 (value-of exp1 nameless-env)))
                     (if (expval->bool val1)
                         (value-of exp2 nameless-env)
                         (value-of exp3 nameless-env))))
           (call-exp (proc args)
                     (apply-procedure (expval->proc (value-of proc nameless-env))
                                      (map (lambda (arg)
                                             (value-of arg nameless-env)) args)))
           (nameless-var-exp (n)
                             (apply-nameless-env nameless-env n))
           (nameless-let-exp (exps body)
                             (let [(vals (map (lambda (exp)
                                                (value-of exp nameless-env))
                                              exps))]
                               (value-of body
                                         (extends-nameless-env vals nameless-env))))
           (nameless-proc-exp (body)
                              (proc-val
                               (procedure body nameless-env)))
           (else
            (eopl:error 'invalid-translated-expression "exp: ~s\n" exp)))))

(define value-of-program
  (lambda (pgm)
    (cases program pgm
           (a-program (exp1)
                      (value-of exp1 (empty-nameless-env))))))

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
     ("proc" "(" (arbno identifier) ")" expression)
     proc-exp)
    (expression
     ("(" expression (arbno expression) ")")
     call-exp)
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
     ("let" (arbno identifier "=" expression) "in" expression)
     let-exp)
    (expression
     ("%lexref" number)
     nameless-var-exp)
    (expression
     ("%let" (arbno expression) "in" expression)
     nameless-let-exp)
    (expression
     ("%lexproc" expression)
     nameless-proc-exp)))

(sllgen:make-define-datatypes scanner-let grammar-let)


(define list-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes scanner-let grammar-let)))

(define just-scan
  (sllgen:make-string-scanner scanner-let grammar-let))
(define scan&parse
  (sllgen:make-string-parser scanner-let grammar-let))

;; test cases

(define test-driver
  (lambda (case)
    (letrec [(res (value-of-program (translation-of-program (scan&parse case))))]
      (eopl:printf "case: ~a, result: ~a\n" case res))))

;; DEBUG
#|
(eopl:pretty-print
 (translation-of-program
  (scan&parse "let sum = proc (x) proc (y) +(x, y) in ((sum 2) 3)")))

(value-of-program
 (translation-of-program
  (scan&parse "let sum = proc (x) proc (y) +(x, y) in ((sum 2) 3)")))
|#

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
(test-driver "let x = 30 in let x = -(x,1) y = -(x,2) in -(x,y)")
(test-driver "let f = proc (x) -(x,11) in (f 77)")
(test-driver "let f = proc (x) -(x,11) in (f (f 77))")
;; example of Curried
(test-driver "let sum = proc (x) proc (y) +(x, y) in ((sum 2) 3)")

(test-driver "let f = proc (x y) -(x, y) in (f 3 2)")

#|
在函数只能有单个参数的约束下，实现递归调用的方法
利用柯里化，引入一个额外的参数，绑定要实现递归调用的函数自身
|#
(test-driver "let makemult = proc (maker)
proc (x)
if zero?(x)
then 0
else -(((maker maker) -(x,1)), minus(4))
in let times4 = proc (x) ((makemult makemult) x)
in (times4 3)")

(define sum-impl
  "let sumHelper = proc (nextSum)
                     proc (n)
                       if equal? (n, 1) then
                         1
                       else + (((nextSum nextSum) -(n, 1)), n)
   in let sum = proc(n) ((sumHelper sumHelper) n)
   in (sum 100)")

(test-driver sum-impl)
