#lang racket/base
(require racket/file racket/list racket/string racket/match)
(define labels '("ax-1" "ax-2" "ax-3" "ax-luk1" "ax-luk2" "ax-luk3"
 "ax-frege1" "ax-frege2" "ax-frege8" "ax-frege28" "ax-frege31" "ax-frege41"
 "ax-frege52a" "ax-frege54a" "ax-frege58a"))
(define rows
  (for/list ([l (in-list (cdr (file->lines "SOURCE-LABELS.tsv")))]
             #:when (member (list-ref (string-split l "\t" #:trim? #f) 1) labels))
    (string-split l "\t" #:trim? #f)))
(define (parse-form s)
  (define ts (cdr (string-split s)))
  (define (pop!) (begin0 (car ts) (set! ts (cdr ts))))
  (define (expect! s) (unless (equal? (pop!) s) (error 'parse "expected ~a" s)))
  (define (p)
    (define t (pop!))
    (cond
      [(member t '("ph" "ps" "ch" "th" "ta")) t]
      [(equal? t "-.") (list 'not (p))]
      [(equal? t "if-")
       (expect! "(") (define a (p)) (expect! ",") (define b (p))
       (expect! ",") (define c (p)) (expect! ")") (list 'if a b c)]
      [(equal? t "(")
       (define a (p)) (define op (pop!)) (define b (p)) (expect! ")")
       (list op a b)]
      [else (error 'parse "unexpected token ~a" t)]))
  (define f (p))
  (unless (null? ts) (error 'parse "remaining ~a" ts)) f)
(define (not1 a) (- 1 a))
(define (and1 a b) (* a b))
(define (or1 a b) (max a b))
(define (imp1 a b) (or1 (not1 a) b))
(define (truth f vals)
  (match f
    [(? string? v) (hash-ref vals v)]
    [(list 'not a) (not1 (truth a vals))]
    [(list 'if a b c) (if (= (truth a vals) 1) (truth b vals) (truth c vals))]
    [(list op a b)
     (define x (truth a vals)) (define y (truth b vals))
     (cond [(equal? op "->") (imp1 x y)]
           [(equal? op "<->") (if (= x y) 1 0)]
           [(equal? op "/\\") (and1 x y)]
           [(equal? op "\\/") (or1 x y)]
           [else (error 'truth "operator ~a" op)])]))
(define (variables f)
  (match f [(? string? v) (list v)] [(list 'not a) (variables a)]
    [(list 'if a b c) (remove-duplicates (append (variables a) (variables b) (variables c)))]
    [(list _ a b) (remove-duplicates (append (variables a) (variables b)))]))
(call-with-output-file "LOGIC-BOOLEAN-CHECK.tsv"
  (lambda (out)
    (displayln "label\tvariable_count\tassignments_checked\tfalse_assignments\tresult" out)
    (for ([r (in-list rows)])
      (define f (parse-form (list-ref r 3))) (define vs (variables f))
      (define total (expt 2 (length vs)))
      (define failures
        (for/sum ([a (in-range total)])
          (define vals (for/hash ([v (in-list vs)] [i (in-naturals)])
            (values v (if (bitwise-bit-set? a i) 1 0))))
          (if (= (truth f vals) 1) 0 1)))
      (fprintf out "~a\t~a\t~a\t~a\t~a\n" (list-ref r 1) (length vs) total failures
        (if (= failures 0) "TAUTOLOGY" "FAIL"))
      (unless (= failures 0) (error 'truth "failed ~a" (list-ref r 1)))))
  #:exists 'error)
(unless (= (length rows) 15) (error 'count "expected15 got~a" (length rows)))
(printf "checked ~a source axioms\n" (length rows))
