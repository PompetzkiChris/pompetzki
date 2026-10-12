#lang racket/base
(require racket/list racket/file json "registry-auth-v4.rkt")
(define checks 0)
(define failures '())
(define (check label expected actual)
  (set! checks (add1 checks))
  (unless (equal? expected actual)
    (set! failures (cons (hash 'label label 'expected expected 'actual actual) failures))))
(for ([n (in-range 707)])
  (check (format "AST prefix ~a" n) #t (authenticated-prefix? (take canonical-registry n)))
  (check (format "token prefix ~a" n) #t (authenticated-token-prefix? (take canonical-token-entries n))))
(for ([i (in-range 706)])
  (define before (take canonical-registry i))
  (define entry (canonical-registry-entry i))
  (check (format "formula alteration at ~a" i) #f
         (authenticated-prefix? (append before (list (cons (vector 'n (car entry)) (cdr entry))))))
  (check (format "hypothesis alteration at ~a" i) #f
         (authenticated-prefix? (append before (list (cons (car entry) (cons 999 (cdr entry)))))))
  (check (format "token alteration at ~a" i) #f
         (authenticated-token-prefix?
          (append (take canonical-token-entries i) (list (cons "n" (list-ref canonical-token-entries i)))))))
(define zero-tokens
  (for/list ([entry (in-list canonical-token-entries)])
    (for/list ([token (in-list entry)])
      (if (number? token) (string-append "000" (number->string token)) token))))
(check "numeric leading zeros in all 706 entries" #t (authenticated-token-prefix? zero-tokens))
(check "AST prefix of 707 entries" #f (authenticated-prefix? (append canonical-registry (list (car canonical-registry)))))
(check "token prefix of 707 entries" #f (authenticated-token-prefix? (append canonical-token-entries (list (car canonical-token-entries)))))
(check "decimal token is rejected" #f
       (authenticated-token-prefix? (list (map (lambda (x) (if (equal? x 0) "0.0" x)) (car canonical-token-entries)))))
(check "non-list AST input" #f (authenticated-prefix? '#(0)))
(check "non-list token input" #f (authenticated-token-prefix? '#(0)))
(define result (hash 'checks checks 'passed (- checks (length failures)) 'failed (length failures) 'failures (reverse failures)))
(call-with-output-file "registry-api-v4-results.json" #:exists 'error (lambda (out) (write-json result out)))
(write-json result)
(newline)
(unless (null? failures) (exit 1))
