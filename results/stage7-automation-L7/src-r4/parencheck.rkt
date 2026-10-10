#lang racket/base
;; reads each top-level form of a file and prints its first line number and head; stops at the first read error
(define f (vector-ref (current-command-line-arguments) 0))
(define in (open-input-file f))
(port-count-lines! in)
(read-line in)
(let loop ()
  (define-values (ln col pos) (port-next-location in))
  (define x (with-handlers ([exn:fail? (lambda (e) (printf "ERROR after line ~a: ~a\n" ln (exn-message e)) eof)]) (read in)))
  (unless (eof-object? x)
    (printf "~a: ~a\n" ln (if (pair? x) (let ([s (format "~s" x)]) (substring s 0 (min 60 (string-length s)))) x))
    (loop)))
