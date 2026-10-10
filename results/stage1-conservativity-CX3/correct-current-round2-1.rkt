#lang racket/base
(require racket/file racket/string)
(define lane "C:/ClaudeOutput/pompetzki/lanes/CX3")
(define p (string-append lane "/integrate-current-round2-1.rkt"))
(define s (file->string p))
(define old "'package_matches (and same #t)))))]))")
(define new "'package_matches (and same #t))))]))")
(unless (string-contains? s old) (error 'correction "expected original parse failure"))
(define corrected
  (string-replace (string-replace s old new)
                  "integrate-current-round2-1.rkt" "integrate-current-round2-2.rkt"))
(call-with-output-file (string-append lane "/integrate-current-round2-2.rkt")
  #:exists 'error (lambda (o) (display corrected o)))
(displayln "Created a new corrected integration writer; the first writer remains beside it.")
