#lang racket/base
;; emit-eq-v2.rkt -- lane L7, item 1: writes DIR/L7-1-equality.jdg (equality chains and congruence closure), its index,
;; (v1 had a placeholder for the twin; v2 writes the twin literally and makes (mixed 0) the last theorem.)
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
    (set! last-inst inst)))

;; the twin of the last theorem (mixed 0): the same hypotheses, the goal 7 in 8, which does not follow
(define twin (c '(imp (and (pr Emp 0) (pr Emp 1) (pr Sng 2 0) (pr Sng 3 1) (pr Upr 4 0 2) (pr Upr 5 1 3) (pr Suc 6 4) (pr Suc 7 5) (in 8 6)) (in 7 8))))
(define notes
  (emit-file! dir "L7-1-equality" "equality chains (Leibniz steps) and congruence closure over Suc, Sng, Upr, Opr, Emp, App/Fnc"
              build twin))
(write-new (build-path dir "L7-1-equality.manifest.txt") (string-join (append notes (list "chains:") (reverse chain-notes)) "\n"))
