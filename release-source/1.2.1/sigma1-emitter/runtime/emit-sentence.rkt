#lang racket/base
(require racket/file racket/list racket/match racket/port racket/runtime-path
         "emitjdg2-0033.rkt"
         (prefix-in x: "emit2_0033-mod.rkt")
         (only-in "extr-macros-0033.rkt" @))
(define-runtime-path registry-path "REG-0033.txt")
(define (un n) (if (zero? n) '(O) (list 'S (un (sub1 n)))))
(define (bool v) (match v [(list 'True) #t] [(list 'False) #f]))
(define (term s)
  (match s
    [(? exact-nonnegative-integer? n) (list 'Tnum (un n))]
    [(list 'v (? exact-nonnegative-integer? n)) (list 'Tvar (un n))]
    [(list 'S t) (list 'TS (term t))]
    [(list '+ t u) (list 'Tadd (term t) (term u))]
    [(list '* t u) (list 'Tmul (term t) (term u))]
    [_ (error 'term "expected an exact natural number, variable or natural arithmetic term: ~s" s)]))
(define (formula s)
  (match s
    [(list '= t u) (list 'Feq (term t) (term u))]
    [(list '< t u) (list 'Flt (term t) (term u))]
    [(list '<= t u) (list 'Fle (term t) (term u))]
    [(list 'not a) (list 'Fnot (formula a))]
    [(list 'and a b) (list 'Fand (formula a) (formula b))]
    [(list 'or a b) (list 'Fdis (formula a) (formula b))]
    [(list '-> a b) (list 'Fimp (formula a) (formula b))]
    [(list '<-> a b) (list 'Fiff (formula a) (formula b))]
    [(list 'all< t a) (list 'Fall (term t) (formula a))]
    [(list 'ex< t a) (list 'Fex (term t) (formula a))]
    [(list 'all<= t a) (list 'Falle (term t) (formula a))]
    [(list 'ex<= t a) (list 'Fexe (term t) (formula a))]
    [_ (error 'formula "expected a bounded sentence: ~s" s)]))
(define (say fmt . args) (apply printf fmt args) (flush-output))
(define (emit-sentence text out)
  (define datum
    (call-with-input-string text
      (lambda (in)
        (define d (read in))
        (unless (eof-object? (read in)) (error 'input "expected one sentence"))
        d)))
  (define A (formula datum))
  (unless (and (bool (@ x:wfb '(O) A)) (bool (x:boundedb A)))
    (error 'input "sentence must be closed, well formed and bounded"))
  (define registry (file->lines registry-path))
  (unless (equal? registry (map entry-line (lst x:rEGP)))
    (error 'registry "extracted registry differs from the canonical 677 entries"))
  (define true? (bool (@ x:evb '(Nil) A)))
  (say "sentence ~s\nregistry-equal #t closed-well-formed #t bounded #t exact-truth ~a\n" datum true?)
  (define-values (r cpu real gc) (time-apply (lambda () (x:emit A)) '()))
  (define extracted-batch (car r))
  (define batch (lst extracted-batch))
  (match-define (list 'Thm statement _ _ hypotheses) (last batch))
  (define translated (@ x:tr A x:sid))
  (define expected (x:fromf (if true? translated (list 'Neg translated))))
  (unless (and (equal? statement expected) (null? (lst hypotheses)))
    (error 'binding "final statement or hypotheses differ from EmitterOK"))
  (unless (bool (@ x:check_batch x:rEGP extracted-batch))
    (error 'checker "extracted check_batch rejected"))
  (write-jdg out registry batch)
  (say "final-statement-binding #t final-hypotheses-empty #t extracted-check-batch #t\nemit theorems ~a cpu-ms ~a real-ms ~a gc-ms ~a\nwrote ~a\n" (length batch) cpu real gc out))
(module+ main
  (match (vector->list (current-command-line-arguments))
    [(list sentence out) (emit-sentence sentence out)]
    [_ (error 'usage "racket emit-sentence.rkt 'SENTENCE' NEW-OUTPUT.jdg")]))
