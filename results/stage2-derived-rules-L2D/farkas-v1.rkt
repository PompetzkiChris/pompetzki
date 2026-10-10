#lang racket/base
;; farkas-v1.rkt -- lane L2D, derived rule Farkas: a certificate y >= 0 (integers) with y^T A = 0 and y^T b < 0 for an
;; integer system A x <= b (m rows, n unknowns) becomes the closed ZF theorem that the system has no rational solution.
;; Not trusted; checked step by step by core-v1's copy of the checker, then by both judges.
;;
;; Encoding: x_j = (u_j - v_j) / w with u_j, v_j, w in omega, w /= 0. Row i, A_i x <= b_i, multiplied by w and with the
;; negative terms moved across, is  L_i(z) + d_i = R_i(z)  for some d_i in omega, z = (u_1..u_n, v_1..v_n, w):
;;     L_i: u_j -> max(a_ij,0), v_j -> max(-a_ij,0), w -> max(-b_i,0);   R_i: u_j -> max(-a_ij,0), v_j -> max(a_ij,0), w -> max(b_i,0)
;; Statement (FormV of forms-v2.rkt, coefficients written as numeral variables k with Bin hypotheses, 0 as o):
;;   forall w p g o (Ctx -> forall k_1..k_C (Bin_val1(k_1) -> ... -> forall z_1..z_N (z_1 in w -> ... -> z_N in w ->
;;        not Emp(z_N) -> not (Row_1 & ... & Row_m))))
;;   Row_i = exists l r d (FormV(Lc_i, z, l) & FormV(Rc_i, z, r) & (d in w & Ad(l,d,r)))
;; Proof: scale row i by y_i (FScale, distributivity), add the rows (FAdd, KX4); y^T A = 0 makes the totals agree in
;; every coefficient but w's, where the left exceeds the right by delta = -y^T b >= 1; FUnit, FAdd and FFun give
;; Lt = Rt + delta w; with Lt + D = Rt, associativity, commutativity and cancellation give delta w + D = 0, so
;; delta w = 0 (KZeroSum), against KMulNZ (delta >= 1, w /= 0).
;; Usage: racket farkas-v1.rkt emit CERT.sexp OUT.jdg      CERT: (farkas (A rows) (b vector) (y vector))
(require racket/list racket/match racket/string racket/file racket/path
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/core-v1.rkt")
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/nd-v3.rkt")
         (except-in (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel-v6.rkt") ids)
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel2-v2.rkt")
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel3-v4.rkt")
         (only-in (file "C:/ClaudeOutput/pompetzki/lanes/L2D/bin-v6.rkt") Bin closed-lemma lem last-consequent dist-inst
                  pred-in trans-w rw-fwd rw-bwd)
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel4-v5.rkt")
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/forms-v2.rkt")
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/forms2-v2.rkt"))
(provide (all-defined-out))

;; (FW N): FormV(c,z,v) -> v in w
(defform FW (key)
  (define N (cadr key))
  (closed-lemma key (+ N N 1)
    (lambda vs (let ([cs (take vs N)] [zs (take (drop vs N) N)] [v (list-ref vs (* 2 N))]) (list (FormV cs zs v))))
    (lambda vs `(in ,(list-ref vs (* 2 N)) 0))
    (lambda (k . vs)
      (define cs (take vs N)) (define zs (take (drop vs N) N)) (define v (list-ref vs (* 2 N)))
      (form-open k cs zs v (have k (FormV cs zs v))
        (lambda (k2 ts ss)
          (if (= N 1) (mul-w k2 (car cs) (car zs) v)
              (add-w k2 (if (null? ss) (car ts) (last ss)) (last ts) v)))))))

(define (row-coeffs A b i n)
  (define a (list-ref A i)) (define bi (list-ref b i))
  (values (append (for/list ([x a]) (max x 0)) (for/list ([x a]) (max (- x) 0)) (list (max (- bi) 0)))
          (append (for/list ([x a]) (max (- x) 0)) (for/list ([x a]) (max x 0)) (list (max bi 0)))))
(define (Row Lcs Rcs zs)
  (define l (gs 'l)) (define r (gs 'r)) (define d (gs 'd))
  `(ex ,l (ex ,r (ex ,d (and (and ,(FormV Lcs zs l) ,(FormV Rcs zs r)) (and (in ,d 0) ,(Ad l d r)))))))
(define (bconj-dsl* xs) (bconj-dsl xs))

;; the statement, with coefficient variables kvars (value -> variable) and unknowns zs
(define (farkas-body A b kv zs)
  (define m (length A)) (define n (length (car A)))
  (define (cv x) (if (= x 0) 3 (hash-ref kv x)))
  (define rows (for/list ([i m]) (let-values ([(L R) (row-coeffs A b i n)]) (Row (map cv L) (map cv R) zs))))
  (bconj-dsl rows))

(define (farkas-thm! key A b y)
  (define m (length A)) (define n (length (car A))) (define N (+ n n 1))
  ;; certificate check
  (for ([yi y]) (when (< yi 0) (error 'farkas "negative multiplier")))
  (for ([j n]) (unless (= 0 (for/sum ([i m]) (* (list-ref y i) (list-ref (list-ref A i) j)))) (error 'farkas "y^T A /= 0 at column ~a" j)))
  (define ytb (for/sum ([i m]) (* (list-ref y i) (list-ref b i))))
  (unless (< ytb 0) (error 'farkas "y^T b = ~a is not negative" ytb))
  (define vals (sort (remove-duplicates (filter positive? (append (for*/list ([r A] [x r]) (abs x)) (map abs b)))) <))
  (define C (length vals))
  (begin-thm! key (+ 4 C N))
  (define kvars (for/list ([i C]) (+ 4 i)))
  (define zs (for/list ([i N]) (+ 4 C i)))
  (define kv (for/hash ([v vals] [x kvars]) (values v x)))
  (define H (farkas-body A b kv zs))
  (define k0 (apply cx+ (kctx) (append (for/list ([v vals] [x kvars]) (Bin v x)) (for/list ([z zs]) `(in ,z 0)) (list `(not (pr Emp ,(last zs))) H))))
  ;; canonical numerals: value -> variable; extended on demand
  (define canon (make-hash (cons (cons 0 3) (hash->list kv))))
  (define (num-of k v) (hash-ref canon v))
  (define (num-in k v) (if (= v 0) (zerow k 3) (lem k `(BinW ,v) (list (hash-ref canon v)))))
  ;; all values needed
  (define rowsLR (for/list ([i m]) (let-values ([(L R) (row-coeffs A b i n)]) (cons L R))))
  (define act (for/list ([i m] #:when (> (list-ref y i) 0)) i))
  (define scaled (for/hash ([i act]) (values i (cons (map (lambda (c) (* (list-ref y i) c)) (car (list-ref rowsLR i)))
                                                     (map (lambda (c) (* (list-ref y i) c)) (cdr (list-ref rowsLR i)))))))
  (define partial                                  ; running sums of the scaled coefficient vectors over the active rows
    (let loop ([is act] [accL #f] [accR #f] [out '()])
      (if (null? is) (reverse out)
          (let* ([s (hash-ref scaled (car is))]
                 [L (if accL (map + accL (car s)) (car s))] [R (if accR (map + accR (cdr s)) (cdr s))])
            (loop (cdr is) L R (cons (cons L R) out))))))
  (define KLf (car (last partial))) (define KRf (cdr (last partial)))
  (for ([j (sub1 N)]) (unless (= (list-ref KLf j) (list-ref KRf j)) (error 'farkas "coefficients differ at ~a" j)))
  (define delta (- (last KLf) (last KRf)))
  (unless (= delta (- ytb)) (error 'farkas "delta ~a" delta))
  (define needed (remove-duplicates (filter positive? (append (map (lambda (i) (list-ref y i)) act)
                                                              (append* (for/list ([s (hash-values scaled)]) (append (car s) (cdr s))))
                                                              (append* (for/list ([p partial]) (append (car p) (cdr p))))
                                                              (list delta)))))
  (define new-vals (filter (lambda (v) (not (hash-ref canon v #f))) needed))
  (define result
    (chain-ex k0 (for/list ([v new-vals]) (lambda (k) (lemma-fact k `(BinEx ,v))))
      (lambda (k1 nvars)
        (for ([v new-vals] [x nvars]) (hash-set! canon v x))
        (define (cvar v) (hash-ref canon v))
        (define zin (for/list ([z zs]) (have k1 `(in ,z 0))))
        ;; rows
        (define Hf (have k1 H))
        (define row-facts
          (let loop ([k k1] [i 0] [acc '()] [Hl Hf])
            (if (= i m) (cons k (reverse acc))
                (let-values ([(L R) (values (car (list-ref rowsLR i)) (cdr (list-ref rowsLR i)))])
                  (define Ri (have k (Row (map cvar L) (map cvar R) zs) Hl))
                  (ex-e k Ri (lambda (k2 l)
                    (ex-e k2 (have k2 (last (cx-hyps k2))) (lambda (k3 r)
                      (ex-e k3 (have k3 (last (cx-hyps k3))) (lambda (k4 d)
                        (loop k4 (add1 i) (cons (list l r d) acc) Hl))))))))))))
        row-facts))))
  result)
