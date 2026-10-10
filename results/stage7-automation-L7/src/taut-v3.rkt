#lang racket/base
;; taut-v3.rkt -- lane L7, item 2: the hybrid emitter. At each node sigma of the split tree, the judges' cost of the single
;; step sigma -> phi is measured with the capped copy of taut_bf; at or under the budget it is a leaf (that step, then the box),
;; above it the node splits. The root with sigma empty: one tautology step when phi itself is under the budget.
;; Every tautology step written costs at most max(budget, O(|sigma|)) calls.
(require "l7core-v1.rkt" "omega-base-v1.rkt" "taut-v2.rkt" racket/list racket/match)
(provide (all-from-out "taut-v2.rkt") taut-hybrid! hybrid-thm! conj-perm)
(define (taut-hybrid! phi budget)
  (define-values (atl idx) (atoms-of phi))
  (define atv (list->vector atl))
  (define B (box phi))
  (define bi (box-in phi))
  (define (lit v val) (if val (vector-ref atv v) (Neg (vector-ref atv v))))
  (define (conj s) (for/fold ([acc (car s)]) ([l (cdr s)]) (Kf acc l)))
  (define (direct-ok? s) (eq? #t (car (taut-capped (if (null? s) phi (Imp (conj s) phi)) budget))))
  (define (node s b)
    (cond
      [(eq? b 'BF) (error 'taut-hybrid "not a tautology")]
      [(direct-ok? s) (define l (T '() (Imp (conj s) phi))) (T (list l bi) (Imp (conj s) B))]
      [else
       (define v (split-var b))
       (define l1 (node (append s (list (lit v #t))) (bsubst v #t b)))
       (define l0 (node (append s (list (lit v #f))) (bsubst v #f b)))
       (T (list l1 l0) (if (null? s) B (Imp (conj s) B)))]))
  (define b0 (tobf (topf idx phi)))
  (if (direct-ok? '()) (T '() phi) (M (node '() b0) (box-out phi))))
;; the theorem phi; returns (list steps largest-test-in-this-theorem)
(define (hybrid-thm! key phi budget)
  (define n (add1 (max-free phi)))
  (define s0 (hash-ref stats 'steps 0))
  (define m0 (hash-ref stats 'taut-max 0))
  (hash-set! stats 'taut-max 0)
  (lemma! key n (lambda () (taut-hybrid! phi budget)))
  (define m1 (hash-ref stats 'taut-max 0))
  (hash-set! stats 'taut-max (max m0 m1))
  (list (- (hash-ref stats 'steps 0) s0) m1))
;; (a1 or b1) & ... & (an or bn)  ->  the same conjunction in reverse order (exponential in every split order)
(define (conj-perm n)
  (define cls (for/list ([i n]) (Df (at (* 2 i)) (at (add1 (* 2 i))))))
  (Imp (conj* cls) (conj* (reverse cls))))
