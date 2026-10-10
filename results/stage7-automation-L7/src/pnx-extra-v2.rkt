#lang racket/base
;; pnx-extra-v2.rkt -- lane L7, item 3: additions to pnx-v1.rkt. (v1 used box for the counter; l7core exports box, the vacuous
;; forall, which shadowed it; v2 counts in a one-cell vector.)
;;  - dn-simp: the matrix of a prenex form without double negations, with the line P <-> P' (congruence under each binder);
;;  - pnx2-thm!: the theorem f <-> pi'(f), pi' = dn-simp(pi(f));
;;  - random formulas over the registered symbols (exact LCG) for the test set.
(require "l7core-v1.rkt" "omega-base-v1.rkt" "pnx-v1.rkt" racket/list racket/match)
(provide (all-defined-out))

(define (strip-nn f)
  (match f [(list 'N (list 'N a)) (strip-nn a)] [(list 'N a) (Neg (strip-nn a))] [(list 'I a b) (Imp (strip-nn a) (strip-nn b))] [_ f]))
(define (dn-simp P)
  (cond
    [(qfree? P) (define P2 (strip-nn P)) (values P2 (T '() (Qf P P2)))]
    [(body-of-ex P) => (lambda (B) (define v (fresh!)) (define-values (q l) (dn-simp (inst0 B v))) (values (Xf (abs0 q v)) (ex-cong v l)))]
    [else (match-define (list 'A B) P) (define v (fresh!)) (define-values (q l) (dn-simp (inst0 B v))) (values (All (abs0 q v)) (all-cong v l))]))
(define (pnx2-thm! key f)
  (define n (max 1 (add1 (max-free f))))
  (define pi #f)
  (lemma! key n (lambda ()
                  (define-values (p l) (pnx f))
                  (define-values (p2 l2) (dn-simp p))
                  (set! pi p2)
                  (T (list l l2) (Qf f p2))))
  pi)

;; random formulas: free variables 0..nf-1
(define q-lcg 20261009)
(define (qrand k)
  (set! q-lcg (modulo (+ (* q-lcg 6364136223846793005) 1442695040888963407) 18446744073709551616))
  (modulo (arithmetic-shift q-lcg -33) k))
(define (qpick l) (list-ref l (qrand (length l))))
(define (rand-qf nf depth [bound '()] [counter (make-vector 1 0)])
  (define vars (append (range nf) bound))
  (define (atom)
    (case (qrand 6)
      [(0 1) `(in ,(qpick vars) ,(qpick vars))]
      [(2) `(eq ,(qpick vars) ,(qpick vars))]
      [(3) `(pr Suc ,(qpick vars) ,(qpick vars))]
      [(4) `(pr Opr ,(qpick vars) ,(qpick vars) ,(qpick vars))]
      [else `(pr Emp ,(qpick vars))]))
  (if (= depth 0) (atom)
      (case (qrand 10)
        [(0) `(not ,(rand-qf nf (sub1 depth) bound counter))]
        [(1 2) `(imp ,(rand-qf nf (sub1 depth) bound counter) ,(rand-qf nf (sub1 depth) bound counter))]
        [(3) `(and ,(rand-qf nf (sub1 depth) bound counter) ,(rand-qf nf (sub1 depth) bound counter))]
        [(4) `(or ,(rand-qf nf (sub1 depth) bound counter) ,(rand-qf nf (sub1 depth) bound counter))]
        [(5 6) (let ([x (string->symbol (format "x~a" (begin0 (vector-ref counter 0) (vector-set! counter 0 (add1 (vector-ref counter 0))))))])
                 `(all ,x ,(rand-qf nf (sub1 depth) (cons x bound) counter)))]
        [(7 8) (let ([x (string->symbol (format "x~a" (begin0 (vector-ref counter 0) (vector-set! counter 0 (add1 (vector-ref counter 0))))))])
                 `(ex ,x ,(rand-qf nf (sub1 depth) (cons x bound) counter)))]
        [else (atom)])))
