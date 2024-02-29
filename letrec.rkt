#lang eopl
;; (require racket/trace)

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var symbol?)
   (val expval?)
   (env environment?))
  (extend-env-rec
   (p-name symbol?)
   (b-var list-of-symbol?)
   (body expression?)
   (env environment?)))

;; (test-driver "let f = proc (x) -(x,11) in (f 77)")

(define apply-env
  (lambda (env search-var)
    (cases environment env
           (empty-env ()
                      (eopl:error 'bind "nobinding fournd: ~s" search-var))
           (extend-env (saved-var saved-val saved-env)
                       (if (eqv? search-var saved-var)
                           saved-val
                           (apply-env saved-env search-var)))
           (extend-env-rec (p-name b-vars p-body saved-env)
                           (if (eqv? search-var p-name)
                               (proc-val (procedure b-vars p-body env))
                               (apply-env saved-env search-var))))))

(define list-of-symbol?
  (lambda (symbols)
    (if (null? symbols)
        #t
        (and (symbol? (car symbols))
             (cdr symbols)))))

(define-datatype proc proc?
  (procedure
   (vars list-of-symbol?)
   (body expression?)
   (saved-env environment?)))

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

(define value-of-program
  (lambda (pgm env)
    (cases program pgm
           (a-program (exp1)
                      (value-of exp1 env)))))

(define extend-env-iter
  (lambda (vars vals env)
    (if (null? vars)
        env
        (extend-env-iter (cdr vars)
                         (cdr vals)
                         (extend-env (car vars) (car vals) env)))))

(define apply-procedure
  (lambda (proc1 vals)
    (cases proc proc1
           (procedure (vars body saved-env)
                      (value-of body (extend-env-iter vars vals saved-env))))))

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
           (proc-exp (vars exp)
                     (proc-val (procedure vars exp env)))
           (letrec-exp (p-name b-vars p-body letrec-body)
                       (value-of letrec-body (extend-env-rec p-name b-vars p-body env)))
           (call-exp (proc args)
                     (apply-procedure (expval->proc (value-of proc env))
                                      (map (lambda (arg)
                                             (value-of arg env)) args)))
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
           (let-exp (vars exps body)
                    ;; TODO add error out when vars is null
                    (letrec [(vals (map (lambda (exp)
                                          (value-of exp env)) exps))
                             ]
                      (value-of body
                                (extend-env-iter vars vals env)))))))

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
     ("letrec" identifier "(" (arbno identifier) ")" "=" expression "in" expression)
     letrec-exp)
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
    (letrec [(env (empty-env))
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

(define rec-simple-test
  "letrec double(x)
          = if zero?(x) then 0 else +((double -(x,1)), 2)
   in (double 6)")

(test-driver rec-simple-test)
