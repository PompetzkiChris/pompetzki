#lang racket/base
;; emit-eq-v1.rkt -- lane L7, item 1: writes DIR/L7-1-equality.jdg (equality chains and congruence closure), its index,
;; mutants and manifest lines (with the one-step tautology cost of each chain for comparison).
(require "l7core-v1.rkt" "omega-base-v1.rkt" "eq-v1.rkt" racket/list racket/match racket/string)
(define dir (vector-ref (current-command-line-arguments) 0))
(load-base!)

;; random congruence instances: (list name V hyps goal) or #f
(define (random-instance i V nh)
  (define syms '(eq eq Suc Suc Opr Sng Upr Emp App Fnc in Sub))
  (define hyps
    (remove-duplicates
     (for/list ([k nh])
       (define s (list-ref syms (erand (length syms))))
       (define (r) (erand V))
       (case s
         [(eq) `(eq ,(r) ,(r))] [(in) `(in ,(r) ,(r))] [(Sub) `(pr Sub ,(r) ,(r))]
         [(Suc Sng) `(pr ,s ,(r) ,(r))] [(Opr Upr) `(pr ,s ,(r) ,(r) ,(r))] [(Emp Fnc) `(pr ,s ,(r))]
         [(App) `(pr App ,(r) ,(r) ,(r))]))))
  (define find (pure-closure V hyps))
  (define direct (for/list ([A hyps] #:when (eq? (asym A) 'eq)) (aargs A)))
  (define pairs (for*/list ([u V] [v V] #:when (and (< u v) (= (find u) (find v))
                                                    (not (member (list u v) direct)) (not (member (list v u) direct))))
                  (list u v)))
  (define goal
    (cond [(pair? pairs) `(eq ,@(list-ref pairs (erand (length pairs))))]
          [else (for/first ([A hyps] #:when (and (memq (asym A) '(in Sub))
                                                 (for/or ([x (aargs A)]) (for/or ([v V]) (and (not (= v x)) (= (find v) (find x)))))))
                  (mk (asym A) (map (lambda (x) (or (for/first ([v V] #:when (and (not (= v x)) (= (find v) (find x)))) v) x)) (aargs A))))]))
  (and goal (list (format "random ~a" i) V hyps goal)))

(define chain-notes '())
(define last-inst #f)
(define (build)
  ;; (a) chains
  (for ([n '(1 2 3 5 8 13 21 34 55)])
    (define orient (for/list ([i n]) (= 0 (erand 2))))
    (define s0 (hash-ref stats 'steps 0))
    (chain-thm! `(Chain ,n) orient)
    (match-define (list ok calls) (chain-one-step-cost orient))
    (set! chain-notes (cons (format "  chain ~a: ~a steps; the whole chain as one tautology step: ~a, ~a taut_bf calls"
                                    n (- (hash-ref stats 'steps 0) s0) (if ok "tautology" "NOT a tautology") calls)
                            chain-notes)))
  ;; (b) congruence closure
  (define insts
    (append (for/list ([k '(1 2 3 5 8 12)]) (suc-ladder k))
            (for/list ([k '(1 2 3 5 8 12)]) (suc-inj-ladder k))
            (for/list ([k '(1 2 3 4 6)]) (pair-tower k))
            (for/list ([k '(1 2 3 4 6)]) (pair-untower k))
            (for/list ([k '(1 2 3 5 8)]) (app-chain k))
            (list (mixed 0))
            (filter values (for/list ([i 40]) (random-instance i 12 14)))))
  (for ([inst insts] [i (in-naturals)])
    (match-define (list name V hyps goal) inst)
    (define r (cc-thm! `(CC ,i ,name) V hyps goal))
    (unless r (error 'emit "~a: the goal does not follow" name))
    (set! last-inst inst)))

;; the twin of the last theorem: the same hypotheses with a goal that does not follow by congruence
(define notes
  (emit-file! dir "L7-1-equality" "equality chains (Leibniz steps) and congruence closure over Suc, Sng, Upr, Opr, Emp, App/Fnc"
              build
              (lambda-twin)))
