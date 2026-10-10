#lang racket/base
;; emit-taut-v1.rkt -- lane L7, item 2: writes DIR/L7-2-tautologies.jdg (the hybrid split emitter, budget 2000 taut_bf calls
;; per step) and DIR/L7-2-direct-control.jdg (some of the same tautologies as single tautology steps, to time the judges on
;; the unsplit form), with indexes, mutants and manifests.
(require "l7core-v1.rkt" "omega-base-v1.rkt" "taut-v3.rkt" "mutants-v2.rkt" racket/list racket/match racket/string)
(define dir (vector-ref (current-command-line-arguments) 0))
(load-base!)
(define BUDGET 2000)
(define CAP 1000000)

(define (unsat-3cnf n m)                 ; the next random 3-CNF that is unsatisfiable (its negation a tautology)
  (let loop ()
    (define f (random-3cnf n m))
    (define-values (atl idx) (atoms-of f))
    (if (tree-size (tobf (topf idx f))) f (loop))))
(define formulas
  (append (for/list ([n '(8 12 16 20 24 28)]) (list (format "clauses-em ~a" n) (clauses-em n)))
          (for/list ([n '(4 6 8 10)]) (list (format "conj-perm ~a" n) (conj-perm n)))
          (for/list ([n '(2 3 4)]) (list (format "php ~a" n) (php n)))
          (for/list ([n '(12 16 20)] [k (in-naturals)]) (list (format "3cnf-unsat ~a ~a" n (* 6 n)) (unsat-3cnf n (* 6 n))))
          (list (list "rev-chain 40" (rev-chain 40)))))
(define rows '())
(define (build)
  (for ([e formulas] [i (in-naturals)])
    (match-define (list name phi) e)
    (define-values (atl idx) (atoms-of phi))
    (match-define (list d dcalls) (taut-capped phi CAP))
    (match-define (list steps mx) (hybrid-thm! `(Taut ,i ,name) phi BUDGET))
    (set! rows (cons (format "  ~a: atoms ~a, size ~a; one tautology step: ~a; split: ~a steps, largest step ~a calls"
                             name (length atl) (form-size phi)
                             (if (eq? d 'cap) (format "more than ~a calls" CAP) (format "~a calls" dcalls)) steps mx)
                     rows))))
(define twin (Imp (Mem 0 1) (Mem 0 2)))
(define notes (emit-file3! dir "L7-2-tautologies" (format "large tautologies split so that every tautology step stays under ~a taut_bf calls" BUDGET)
                           build twin))
(write-new (build-path dir "L7-2-tautologies.manifest.txt") (string-join (append notes (list "formulas:") (reverse rows)) "\n"))

;; the control file: single tautology steps
(define control (list (list "clauses-em 8" (clauses-em 8)) (list "clauses-em 12" (clauses-em 12)) (list "clauses-em 16" (clauses-em 16))
                      (list "conj-perm 6" (conj-perm 6)) (list "conj-perm 8" (conj-perm 8))))
(define crows '())
(define (build-control)
  (for ([e control] [i (in-naturals)])
    (match-define (list name phi) e)
    (define n (add1 (max-free phi)))
    (lemma! `(Direct ,i ,name) n (lambda () (T '() phi)))
    (set! crows (cons (format "  ~a: one tautology step, ~a calls" name (cadr (taut-capped phi CAP))) crows))))
(define cnotes (emit-file3! dir "L7-2-direct-control" "control: the same tautologies as single tautology steps" build-control twin))
(write-new (build-path dir "L7-2-direct-control.manifest.txt") (string-join (append cnotes (list "formulas:") (reverse crows)) "\n"))
