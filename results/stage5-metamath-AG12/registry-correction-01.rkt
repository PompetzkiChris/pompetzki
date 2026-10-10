#lang racket
(require racket/file racket/string)
(define source (file->string "registry-reader.rkt"))
(define corrected (string-replace source "\\\\r?\\\\ntext zi_f" "\\r?\\ntext zi_f"))
(unless (not (equal? source corrected)) (error 'correction "target absent"))
(call-with-output-file "registry-reader-v2.rkt" #:exists 'error
  (lambda (out) (display corrected out)))
