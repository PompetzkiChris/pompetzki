#lang racket/base
(require racket/file racket/string)
(define lane "C:/ClaudeOutput/pompetzki/lanes/CX3")
(define s (file->string (string-append lane "/integrate-current-round2-3.rkt")))
(define replacements
  (list
   (cons "(define sr (source cert-name))"
         "(define sr (and (compile-ok? mod) (source cert-name)))")
   (cons "(define dr (source (string-append data-mod \".v\")))"
         "(define dr (and (compile-ok? data-mod) (source (string-append data-mod \".v\"))))")
   (cons "(define object (record (build-path owner (string-append mod \".vo\"))))"
         "(define object (and (compile-ok? mod) (record (build-path owner (string-append mod \".vo\")))))")
   (cons "(define data-object (record (build-path owner (string-append data-mod \".vo\"))))"
         "(define data-object (and (compile-ok? data-mod) (record (build-path owner (string-append data-mod \".vo\")))))")
   (cons "integrate-current-round2-3.rkt" "integrate-current-round2-4.rkt")))
(define corrected
  (for/fold ([text s]) ([p (in-list replacements)])
    (unless (string-contains? text (car p)) (error 'correction "missing expected expression: ~a" (car p)))
    (string-replace text (car p) (cdr p))))
(call-with-output-file (string-append lane "/integrate-current-round2-4.rkt")
  #:exists 'error (lambda (o) (display corrected o)))
(displayln "Created a new writer that records source and object artifacts only after their compiler receipt completes.")
