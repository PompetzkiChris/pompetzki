#lang racket/base
;; tables-v2.rkt -- lane L7: markdown tables from the judge rows (judge-run-v1.rkt's format) of the given result files.
;; (v1 was written through a shell here-document that dropped the doubled backslashes of its regular expressions.)
;; Usage: racket tables-v2.rkt OUT.md RESULT.txt ...
(require racket/list racket/string racket/match racket/file)
(define args (vector->list (current-command-line-arguments)))
(define rows (append* (for/list ([f (cdr args)]) (file->lines f))))
(define (parse r)
  (match (regexp-match #px"^(\\S+) \\| pmp (\\S+) exit (\\d+) (\\d+) ms \\| racket (\\S+) exit (\\d+) (\\d+) ms \\| pmp: (.*) \\| racket: (.*)$" r)
    [(list _ f pv pe pt rv re rt po ro) (list f pv pe (string->number pt) rv re (string->number rt) po ro)]
    [_ (error 'parse "row: ~a" r)]))
(define ps (map parse rows))
(define (short f) (let ([m (regexp-match #px"lanes/L7/out/(.*)$" f)]) (if m (cadr m) f)))
(define (secs ms) (format "~a.~a s" (quotient ms 1000) (quotient (remainder ms 1000) 100)))
(define files (filter (lambda (p) (not (regexp-match? #rx"/mut/" (car p)))) ps))
(define muts (filter (lambda (p) (regexp-match? #rx"/mut/" (car p))) ps))
(define (pmp-where po) (let ([m (regexp-match #px"theorem and step \\(counted from 0\\): (\\d+) (\\d+)" po)]) (if m (format "~a ~a" (cadr m) (caddr m)) "")))
(define (pmp-why po) (let ([m (regexp-match #px"^REJECT (.*?) theorem and step" po)]) (if m (cadr m) po)))
(define (rk-where ro) (let ([m (regexp-match #px"REJECT theorem (\\d+) step (\\d+) \\((.*)\\)" ro)]) (if m (format "~a ~a (~a)" (cadr m) (caddr m) (cadddr m)) ro)))
(define out
  (string-append
   "| file | pmp | pmp time | Racket | Racket time | Racket's count (registry, theorems, steps, final registry) |\n|---|---|---:|---|---:|---|\n"
   (string-join (for/list ([p files])
                  (match-define (list f pv pe pt rv re rt po ro) p)
                  (format "| ~a | ~a, exit ~a | ~a | ~a, exit ~a | ~a | ~a |" (short f) pv pe (secs pt) rv re (secs rt)
                          (let ([m (regexp-match #px"ACCEPT registry (\\d+) theorems (\\d+) steps (\\d+) final-registry (\\d+)" ro)]) (if m (string-join (cdr m) ", ") ""))))
                "\n")
   (format "\n\nsums over these files: pmp ~a ms, Racket ~a ms\n\n" (apply + (map cadddr files)) (apply + (map (lambda (p) (list-ref p 6)) files)))
   "| mutant | pmp | Racket | pmp: theorem step, reason | Racket: theorem step (rule) |\n|---|---|---|---|---|\n"
   (string-join (for/list ([p muts])
                  (match-define (list f pv pe pt rv re rt po ro) p)
                  (format "| ~a | ~a, exit ~a | ~a, exit ~a | ~a: ~a | ~a |" (short f) pv pe rv re (pmp-where po) (pmp-why po) (rk-where ro)))
                "\n")
   (format "\n\ncounts: files ~a (~a ACCEPT by both), mutants ~a (~a REJECT by both)\n"
           (length files) (count (lambda (p) (and (equal? (list-ref p 1) "ACCEPT") (equal? (list-ref p 4) "ACCEPT"))) files)
           (length muts) (count (lambda (p) (and (equal? (list-ref p 1) "REJECT") (equal? (list-ref p 4) "REJECT"))) muts))))
(call-with-output-file (car args) #:exists 'error (lambda (o) (write-string out o)))
(display out)
