#lang racket/base
;; taut-v2.rkt -- lane L7, item 2: taut-v1.rkt plus a benchmark family of linear size. (taut-v1's junk-em uses an iff chain,
;; whose N/I form doubles at every iff: size 4^n; it is kept but not used.)
;; B1': (a1 or b1) & ... & (an or bn), or (q or not q). Leftmost order: about 2^n branches before q is reached.
(require "l7core-v1.rkt" "taut-v1.rkt" racket/list)
(provide (all-from-out "taut-v1.rkt") clauses-em)
(define (clauses-em n)
  (Df (conj* (for/list ([i n]) (Df (at (* 2 i)) (at (add1 (* 2 i)))))) (Df (at (* 2 n)) (Neg (at (* 2 n))))))
