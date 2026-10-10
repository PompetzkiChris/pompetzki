#lang racket/base
(require racket/file racket/list)
(define scheme-lines (filter (lambda (l) (not (regexp-match? #rx"^\\(load " l))) (file->lines "../provenance/emit2_0033.scm")))
(define module-lines (drop (file->lines "emit2_0033-mod.rkt") 4))
(unless (equal? scheme-lines module-lines) (error 'source-binding "Racket module body differs from Scheme extraction"))
(printf "Racket-module-body-equals-Scheme-extraction-after-loader-removal #t\n")
