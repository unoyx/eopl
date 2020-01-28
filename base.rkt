#lang eopl

(provide empty-env)
(provide extend-env)
(provide apply-env)
(provide scanner-spec-a)
(provide report-expval-extractor-error)

(define (empty-env)
  (lambda (search-var)
    (report-no-binding-found search-var)))

(define (extend-env saved-var saved-val saved-env)
  (lambda (search-var)
    (if (eqv? search-var saved-var)
        saved-val
        (apply-env saved-env search-var))))

(define (apply-env env search-val)
  (env search-val))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))

(define (report-expval-extractor-error type val)
  (eopl:printf "Expval extractor error type: ~s value: ~s" type val))

(define scanner-spec-a
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)))

