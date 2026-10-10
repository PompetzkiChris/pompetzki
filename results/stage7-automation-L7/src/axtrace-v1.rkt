#lang racket/base
;; axtrace-v1.rkt -- lane L7: the axiom trace of a JDG1 file: for each theorem the registry axioms (entries 0..6: Ext Pair
;; Union Power Inf Found Choice) it reaches through U steps and earlier theorems, whether it reaches a Separation or a
;; Collection instance (Y steps of those shapes), and how many definitions. Usage: racket axtrace-v1.rkt FILE.jdg [KEYS.index]
(require "l7core-v1.rkt" racket/list racket/match racket/string racket/file racket/set)
(define args (vector->list (current-command-line-arguments)))
(define-values (rg ths) (read-jdg-text (file->string (car args))))
(define nrg (length rg))
(define AX '#("Ext" "Pair" "Union" "Power" "Inf" "Found" "Choice"))
(define tv (list->vector ths))
(define memo (make-hash))
(define (trace i)
  (hash-ref! memo i
    (lambda ()
      (for/fold ([acc (set)]) ([st (caddr (vector-ref tv i))])
        (match st
          [(list 'U r _) (cond [(< r 7) (set-add acc (vector-ref AX r))]
                               [(< r nrg) (set-add acc 'def)]
                               [else (set-union acc (trace (- r nrg)))])]
          [(list 'Y g) (let ([f (tof g)]) (cond [(isSepN f) (set-add acc "Sep")] [(isCollN f) (set-add acc "Coll")] [else acc]))]
          [_ acc])))))
(define all (for/fold ([acc (set)]) ([i (vector-length tv)]) (set-union acc (trace i))))
(define (fmt s) (string-join (sort (for/list ([x s]) (if (symbol? x) "definitions" x)) string<?) " "))
(printf "file: ~a\n  union over all ~a theorems: ~a\n" (car args) (vector-length tv) (fmt all))
(printf "  last theorem: ~a\n" (fmt (trace (sub1 (vector-length tv)))))
