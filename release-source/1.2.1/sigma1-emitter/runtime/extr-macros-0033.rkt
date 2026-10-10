#lang racket/base
;; extr-macros-0033.rkt - lane L2R, 2026-10-10. Racket versions of the three macros that Rocq's Scheme
;; extraction relies on (lambdas, @, match). Constructors are lists headed by a symbol: `(S ,n), (O).
(require (prefix-in r: racket/match) (for-syntax racket/base))
(provide lambdas @ match)
(define-syntax lambdas
  (syntax-rules ()
    [(_ () b) (lambda () b)]
    [(_ (a) b) (lambda (a) b)]
    [(_ (a r ...) b) (lambda (a) (lambdas (r ...) b))]))
(define-syntax @
  (syntax-rules ()
    [(_ f) (f)]
    [(_ f a) (f a)]
    [(_ f a r ...) (@ (f a) r ...)]))
(define-syntax (match stx)
  (syntax-case stx ()
    [(_ e cl ...)
     (with-syntax ([(rcl ...)
                    (for/list ([c (syntax->list #'(cl ...))])
                      (syntax-case c ()
                        [((k x ...) b) #'[(list 'k x ...) b]]
                        [(w b) #'[_ b]]))])
       #'(r:match e rcl ... [v (error 'match "no clause for ~a" (if (pair? v) (car v) v))]))]))
