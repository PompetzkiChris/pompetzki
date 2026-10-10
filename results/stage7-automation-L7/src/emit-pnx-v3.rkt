#lang racket/base
;; emit-pnx-v3.rkt -- lane L7, item 3: writes DIR/L7-3-quantifiers.jdg: for hand-picked and random formulas f over the
;; registered symbols, the theorem f <-> pi(f) with pi(f) prenex (matrix without double negations); index, mutants, manifest.
(require "l7core-v1.rkt" "omega-base-v1.rkt" "pnx-v1.rkt" "pnx-extra-v2.rkt" "mutants-v2.rkt" racket/list racket/match racket/string)
(define dir (vector-ref (current-command-line-arguments) 0))
(load-base!)
(define hand
  (list '(imp (all x (in x 0)) (in 1 0))
        '(not (ex x (and (pr Emp x) (in x 0))))
        '(iff (all x (in x 0)) (ex y (in 0 y)))
        '(and (all x (ex y (pr Opr y x 0))) (not (all z (in z z))))
        '(imp (imp (all x (in x 0)) (ex y (in y 1))) (all z (ex w (pr Suc w z))))
        '(or (all x (ex y (and (in x y) (pr Suc y x)))) (ex u (all v (not (in v u)))))
        '(imp (ex x (pr Suc x 0)) (all y (or (in y 0) (eq y 1))))))
(define rows '())
(define (build)
  (define fs (append hand
                     (let loop ([k 0] [acc '()])
                       (if (= (length acc) 40) (reverse acc)
                           (let ([f (rand-qf 2 4)])
                             (if (qfree? (c f)) (loop (add1 k) acc) (loop (add1 k) (cons f acc))))))))
  ;; the last theorem is the last hand formula, whose twin is written below
  (define order (append (cdr (reverse (reverse fs))) '()))
  (for ([f (append (remove (last hand) fs) (list (last hand)))] [i (in-naturals)])
    (define fc (c f))
    (define s0 (hash-ref stats 'steps 0))
    (define pi (pnx2-thm! `(Pnx ,i) fc))
    (set! rows (cons (format "  ~a: ~a steps, prefix ~a, size ~a -> ~a: ~a  =>  ~a" i (- (hash-ref stats 'steps 0) s0)
                             (prefix-length pi) (form-size fc) (form-size pi) (show fc) (show pi))
                     rows))))
(define twin (let ([f (c (last hand))]) (Qf f (Neg f))))
(define notes (emit-file3! dir "L7-3-quantifiers" "prenex forms with proof: forall-intro, exists-elim, exists-intro, forall-elim, congruence under binders"
                           build twin))
(write-new (build-path dir "L7-3-quantifiers.manifest.txt") (string-join (append notes (list "formulas:") (reverse rows)) "\n"))
