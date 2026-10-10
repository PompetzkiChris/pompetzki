#lang racket/base
;; taut-v1.rkt -- lane L7, item 2: large tautologies split into steps whose Shannon tests stay linear.
;; The judges' tautology test (ReplayT.v taut_bf) always branches on the leftmost atom; its cost is the size of the
;; decision tree in that order, which can be exponential where another order is small. This emitter
;;  - chooses its own split order (the atom whose two restrictions are smallest, a one-step lookahead on the judges' own
;;    simplification mkN/mkI);
;;  - writes, for each node sigma of its tree (a conjunction of literals), the line sigma -> B(phi), where B(phi) is the
;;    vacuous box forall phi^ (Y: phi -> B(phi); V: B(phi) -> phi); to the Shannon test B(phi) is a single atom;
;;  - at a leaf (phi simplifies to T under sigma): T step sigma -> phi (the test assigns sigma's atoms first, as they are
;;    leftmost, then phi is the constant T), and T step [that, phi -> B(phi)] sigma -> B(phi);
;;  - at an inner node: T step [sigma & p -> B, sigma & not p -> B] sigma -> B;
;;  - at the root: B(phi), then V and M give phi.
;; Every tautology step costs O(|sigma|) taut_bf calls.
(require "l7core-v1.rkt" "omega-base-v1.rkt" racket/list racket/match)
(provide (all-defined-out))

;; the judges' test with a cap on the number of taut_bf calls: (list result calls), result #t, #f or 'cap
(define (taut-capped f cap)
  (define-values (atl idx) (atoms-of f))
  (define calls 0)
  (define (go k b)
    (set! calls (add1 calls))
    (cond [(> calls cap) (raise 'cap)]
          [(eq? b 'BT) #t] [(eq? b 'BF) #f]
          [else (let ([v (somevar b)]) (and (> k 0) v (go (sub1 k) (bsubst v #t b)) (go (sub1 k) (bsubst v #f b))))]))
  (with-handlers ([(lambda (e) (eq? e 'cap)) (lambda (e) (list 'cap calls))])
    (list (go (length atl) (tobf (topf idx f))) calls)))

(define (bsize b) (match b [(list 'BN a) (add1 (bsize a))] [(list 'BI a d) (+ 1 (bsize a) (bsize d))] [_ 1]))
(define (bvars b)
  (define s (make-hash))
  (let walk ([b b]) (match b [(list 'BV n) (hash-set! s n #t)] [(list 'BN a) (walk a)] [(list 'BI a d) (walk a) (walk d)] [_ (void)]))
  (sort (hash-keys s) <))
(define (split-var b)
  (for/fold ([best #f] [bc #f] #:result best) ([v (bvars b)])
    (define cst (+ (bsize (bsubst v #t b)) (bsize (bsubst v #f b))))
    (if (or (not bc) (< cst bc)) (values v cst) (values best bc))))
;; the emitter's tree without lines: (list leaves nodes) or #f when some branch is F (not a tautology)
(define (tree-size b)
  (cond [(eq? b 'BT) (list 1 1)] [(eq? b 'BF) #f]
        [else (define v (split-var b))
              (define t1 (tree-size (bsubst v #t b)))
              (define t0 (and t1 (tree-size (bsubst v #f b))))
              (and t0 (list (+ (car t1) (car t0)) (+ 1 (cadr t1) (cadr t0))))]))

;; inside an open theorem: the line phi (phi a tautology), by the split above
(define (taut-split! phi)
  (define-values (atl idx) (atoms-of phi))
  (define atv (list->vector atl))
  (define B (box phi))
  (define bi (box-in phi))
  (define (lit v val) (if val (vector-ref atv v) (Neg (vector-ref atv v))))
  (define (conj s) (for/fold ([acc (car s)]) ([l (cdr s)]) (Kf acc l)))
  (define (node s b)
    (cond
      [(eq? b 'BT) (define l (T '() (Imp (conj s) phi))) (T (list l bi) (Imp (conj s) B))]
      [(eq? b 'BF) (error 'taut-split "not a tautology")]
      [else
       (define v (split-var b))
       (define l1 (node (append s (list (lit v #t))) (bsubst v #t b)))
       (define l0 (node (append s (list (lit v #f))) (bsubst v #f b)))
       (T (list l1 l0) (if (null? s) B (Imp (conj s) B)))]))
  (define b0 (tobf (topf idx phi)))
  (if (eq? b0 'BT) (T '() phi) (M (node '() b0) (box-out phi))))

;; ======================================================================== benchmark tautologies (atoms x0 in x(k+1))
(define (at k) (Mem 0 (add1 k)))
(define (disj ls) (for/fold ([acc (car ls)]) ([l (cdr ls)]) (Df acc l)))
(define (conj* ls) (for/fold ([acc (car ls)]) ([l (cdr ls)]) (Kf acc l)))
(define (iff-chain ks) (if (null? (cdr ks)) (at (car ks)) (Qf (at (car ks)) (iff-chain (cdr ks)))))
;; B1: an iff chain over n atoms, or q or not q   (the leftmost atoms are the chain's)
(define (junk-em n) (Df (iff-chain (range n)) (Df (at n) (Neg (at n)))))
;; B2: (p(n-1) -> pn) -> ... -> (p1 -> p2) -> p1 -> pn
(define (rev-chain n) (foldr Imp (at n) (append (for/list ([i (in-range (sub1 n) 0 -1)]) (Imp (at i) (at (add1 i)))) (list (at 1)))))
;; B3: not (C1 & ... & Cm), random 3-clauses over n atoms (exact LCG); kept only when unsatisfiable
(define t-lcg 20261009)
(define (trand k)
  (set! t-lcg (modulo (+ (* t-lcg 6364136223846793005) 1442695040888963407) 18446744073709551616))
  (modulo (arithmetic-shift t-lcg -33) k))
(define (random-3cnf n m)
  (Neg (conj* (for/list ([j m])
                (disj (for/list ([r 3]) (let ([v (trand n)]) (if (= 0 (trand 2)) (at v) (Neg (at v))))))))))
;; B4: pigeonhole, n+1 pigeons and n holes: not (every pigeon in a hole & no hole holds two)
(define (php n)
  (define (p i j) (at (+ (* i n) j)))
  (Neg (conj* (append (for/list ([i (add1 n)]) (disj (for/list ([j n]) (p i j))))
                      (for*/list ([j n] [i (add1 n)] [k (add1 n)] #:when (< i k)) (Df (Neg (p i j)) (Neg (p k j))))))))
(define (max-free f) (match f [(list (or 'E 'Q) x y) (max x y)] [(list 'P _ a) (apply max 0 a)] [(list 'N a) (max-free a)]
                       [(list 'I a b) (max (max-free a) (max-free b))] [(list 'A a) (max 0 (sub1 (max-free a)))]))
;; the theorem phi, by the split; returns (list steps max-calls)
(define (taut-thm! key phi)
  (define n (add1 (max-free phi)))
  (define s0 (hash-ref stats 'steps 0))
  (lemma! key n (lambda () (taut-split! phi)))
  (- (hash-ref stats 'steps 0) s0))
