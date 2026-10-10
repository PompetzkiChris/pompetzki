#lang racket/base
;; emit-r4-v1.rkt -- lane L7 recovery (after the 19:30 power loss): writes DIR/L7-6-order.jdg (order and cancellation on omega,
;; order2-v4.rkt) and DIR/L7-5-farkas-l2d.jdg (L2D's four certificates f1..f4 through farkas7-v5.rkt), with indexes, manifests
;; and the mutated copies that the copy of the checker rejects (mutants-v2.rkt).
(require "l7core-v1.rkt" "omega-base-v1.rkt" "omega-kind-v5.rkt" "omega-laws-v3.rkt" "order2-v4.rkt" "sums-v4.rkt" "farkas7-v5.rkt"
         "genfarkas-v1.rkt" "mutants-v2.rkt" racket/list racket/match racket/string)
(define dir (vector-ref (current-command-line-arguments) 0))
(load-base!)
(define n1 (emit-file3! dir "L7-6-order" "order and cancellation on omega: Le, Lt, cancellation of Add and Mul, zero sums and products"
                        (lambda () (for ([e ORDER-LEMMAS]) ((caddr e)))) #f))
(write-new (build-path dir "L7-6-order.manifest.txt") (string-join (append n1 (list (format "final registry ~a" nreg))) "\n"))
(define n2 (emit-file3! dir "L7-5-farkas-l2d" "Farkas certificates of L2D (f1..f4): A x <= b has no rational solution"
                        (lambda () (for ([e (l2d-certs)]) (match-define (list name A b y) e) (farkas-thm! `(Farkas ,name) A b y))) #f))
(write-new (build-path dir "L7-5-farkas-l2d.manifest.txt") (string-join (append n2 (list (format "final registry ~a" nreg))) "\n"))
