#lang racket
(require racket/file racket/string)
(define source (file->string "registry-reader-v2.rkt"))
(define old "(define defs\n  (regexp-match* #px\"\\\\(\\\"([^\\\"]+)\\\",\\\\s*\\\\[([^]]*)\\\\],\\\\s*\\\"([^\\\"]*)\\\"\\\\)\"\n                 (assignment-list data-text \"defs\")\n                 #:match-select (lambda (m) (list (second m) (quoted-strings (third m)) (fourth m)))))")
(define new "(define defs\n  (for/list ([m (in-list (regexp-match* #px\"\\\\(\\\"([^\\\"]+)\\\",\\\\s*\\\\[([^]]*)\\\\],\\\\s*\\\"([^\\\"]*)\\\"\\\\)\"\n                                      (assignment-list data-text \"defs\") #:match-select values))])\n    (list (second m) (quoted-strings (third m)) (fourth m))))")
(define corrected (string-replace source old new))
(unless (not (equal? source corrected)) (error 'correction "target absent"))
(call-with-output-file "registry-reader-v3.rkt" #:exists 'error
  (lambda (out) (display corrected out)))
