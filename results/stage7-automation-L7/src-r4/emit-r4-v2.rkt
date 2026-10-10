#lang racket/base
;; emit-r4-v2.rkt -- lane L7 recovery: DIR/L7-5-farkas-cyc.jdg: cyclic chains x1 - x2 <= -1, ..., xk - x1 <= -1 for k = 2..5
;; and the planted systems planted-120/121/122 (genfarkas-v1.rkt, exact LCG), through farkas7-v5.rkt, with mutants.
(require "l7core-v1.rkt" "omega-base-v1.rkt" "omega-kind-v5.rkt" "omega-laws-v3.rkt" "order2-v4.rkt" "sums-v4.rkt" "farkas7-v5.rkt"
         "genfarkas-v1.rkt" "mutants-v2.rkt" racket/list racket/match racket/string)
(define dir (vector-ref (current-command-line-arguments) 0))
(load-base!)
(define certs (append (for/list ([k (in-range 2 6)]) (cyclic k))
                      (for/list ([r 3]) (planted (+ 100 20 r) 1 2))))
(define rows '())
(define n (emit-file3! dir "L7-5-farkas-cyc" "Farkas certificates: cyclic chains and planted systems; A x <= b has no rational solution"
                       (lambda () (for ([e certs]) (match-define (list name A b y) e)
                                    (set! rows (cons (format "  ~a: A ~s b ~s y ~s" name A b y) rows))
                                    (farkas-thm! `(Farkas ,name) A b y))) #f))
(write-new (build-path dir "L7-5-farkas-cyc.manifest.txt") (string-join (append n (list (format "final registry ~a" nreg) "instances:") (reverse rows)) "\n"))
