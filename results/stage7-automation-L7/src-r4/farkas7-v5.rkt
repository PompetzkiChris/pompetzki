#lang racket/base
;; farkas7-v5.rkt -- lane L7 round 2, item 1: Farkas certificates (L2D's format (farkas (A rows) (b vector) (y vector)),
;; integers, y >= 0, y^T A = 0, y^T b < 0) become JDG1 theorems that A x <= b has no rational solution.
;; Encoding (L2D's): x_j = (u_j - v_j)/w with u, v, w in omega, w /= 0; frame variables u_1..u_n = 0..n-1, v_1..v_n =
;; n..2n-1, w = 2n. Row i, multiplied by w, with the negative terms moved across, in unary:
;;   L_i = a_ij copies of u_j (a_ij > 0), |a_ij| copies of v_j (a_ij < 0), |b_i| copies of w (b_i < 0)
;;   R_i = |a_ij| copies of u_j (a_ij < 0), a_ij copies of v_j (a_ij > 0), b_i copies of w (b_i > 0)
;;   Row_i = exists l r d (Ch(L_i,l) & Ch(R_i,r) & Nat d & Add(l,d,r))
;; Statement: Nat u.. & Nat v.. & Nat w & not Emp(w) -> not (Row_1 & ... & Row_m).
;; Proof: unpack the rows; add y_i copies of r_i into one value s, which then has two chains: the concatenation of the
;; lists L_i ++ [d_i] and the concatenation of the lists R_i; sort both (insertion sort, lemmas Ins); y^T A = 0 and
;; y^T b < 0 make the sorted left list the sorted right list followed by delta = -y^T b copies of w and the slacks;
;; Split, ChUq and AddSelf leave a chain whose value is 0, ChZero gives Emp(w), against not Emp(w).
;; (v2 = v1 with finish and natline-c defined before final, and the chain lines of s in the last step; v3 = v2 with the
;;  accumulators of for/lists renamed: v2 called them a and b, which shadowed the vector b; v4 builds the lemmas it uses first;
;;  v5 adds the line of the left chain of s to the step for an empty right side R_i.)
(require "l7core-v1.rkt" "omega-base-v1.rkt" "omega-kind-v5.rkt" "omega-laws-v3.rkt" "order2-v4.rkt" "sums-v4.rkt"
         racket/list racket/match)
(provide (all-defined-out))

(define (rep k x) (for/list ([i k]) x))
(define (row-lists A b n i)
  (define a (list-ref A i)) (define bi (list-ref b i)) (define w (* 2 n))
  (values (sort (append (append* (for/list ([x a] [j (in-naturals)]) (if (> x 0) (rep x j) (rep (- x) (+ n j))))) (rep (max 0 (- bi)) w)) <)
          (sort (append (append* (for/list ([x a] [j (in-naturals)]) (if (< x 0) (rep (- x) j) (rep x (+ n j))))) (rep (max 0 bi) w)) <)))
(define (Row L R)
  (define l (fresh-sym 'l)) (define r (fresh-sym 'r)) (define d (fresh-sym 'd))
  `(ex ,l (ex ,r (ex ,d (and ,(Ch L l) ,(Ch R r) (pr Nat ,d) ,(Add l d r))))))
(define (check-cert A b y)
  (define m (length A)) (define n (length (car A)))
  (and (= (length b) m) (= (length y) m) (andmap (lambda (v) (and (exact-integer? v) (>= v 0))) y)
       (for/and ([j n]) (= 0 (for/sum ([i m]) (* (list-ref y i) (list-ref (list-ref A i) j)))))
       (< (for/sum ([i m]) (* (list-ref y i) (list-ref b i))) 0)))
(define (stable-insert-pos S t) (length (filter (lambda (x) (<= x t)) S)))

;; the lines of an insertion sort of X, no context: forall p (Nats(X) & Ch(X,p) -> Ch(sort X, p)); returns that line
(define (sort-line X)
  (let loop ([j 1] [prev #f] [S (list (car X))])
    (define Xj (take X j))
    (define p (fresh!))
    (define Hj (c (conj* (append (Nats Xj) (list (Ch Xj p))))))
    (define body
      (cond
        [(= j 1) (T '() (Imp Hj (c (Ch S p))))]
        [else
         (define Xp (take X (sub1 j))) (define xj (list-ref X (sub1 j)))
         (define Sp (sort Xp <))
         (obt Hj '() (c (Ch Xj p))
           (lambda (q _ H1)
             (define pos (stable-insert-pos Sp xj))
             (T (list (fa-e prev q) (chnat-line Xp q) (ins-line Sp pos xj q p)) (Imp H1 (c (Ch S p))))))]))
    (define g (G body p))
    (if (= j (length X)) g
        (loop (add1 j) g (let ([xn (list-ref X j)]) (insert-at S (stable-insert-pos S xn) xn))))))

;; the theorem for one certificate; returns (list steps chain-lengths)
(define (farkas-thm! key A b y)
  (base!) (natzero!) (addself!) (zerosum!)
  (unless (check-cert A b y) (error 'farkas "not a certificate: ~a ~a ~a" A b y))
  (define m (length A)) (define n (length (car A))) (define N (add1 (* 2 n))) (define w (* 2 n))
  (define-values (Ls Rs) (for/lists (la lb) ([i m]) (row-lists A b n i)))
  (define zs (range N))
  (define rows (for/list ([L Ls] [R Rs]) (Row L R)))
  (define stmt `(imp (and ,@(Nats zs) (not (pr Emp ,w))) (not ,(conj* rows))))
  (define info #f)
  (lemma! key N
    (lambda ()
      (define H0 (c (conj* (append (Nats zs) (list `(not (pr Emp ,w))) rows))))
      (define goal (c `(pr Emp ,w)))
      ;; unpack row i, then continue with the lists of its values
      (define (unpack i H vals k)
        (cond
          [(= i m) (k H (reverse vals))]
          [else
           (obt H '() (c (list-ref rows i))
             (lambda (l Pl H1)
               (obt H1 '() Pl
                 (lambda (r Pr H2)
                   (obt H2 '() Pr
                     (lambda (d _ H3) (unpack (add1 i) H3 (cons (list l r d) vals) k)))))))]))
      (define (finish H s ALD AR lineLD lineR)
        (define SLD (sort ALD <)) (define SAR (sort AR <))
        (define delta (- (for/sum ([i m]) (* (list-ref y i) (list-ref b i)))))
        (define B (drop SLD (length SAR)))
        (unless (and (equal? (take SLD (length SAR)) SAR) (= (car B) w) (>= (length B) delta))
          (error 'farkas "the sorted lists do not split as expected"))
        (set! info (list (length ALD) (length AR) (length B)))
        (define sLD (T (list lineLD (fa-e (sort-line ALD) s)) (Imp H (c (Ch SLD s)))))
        (cond
          [(null? SAR)
           (T (list sLD lineR (chnat-line ALD s) (chzero-line B s)) (Imp H goal))]
          [else
           (define sR (T (list lineR (fa-e (sort-line AR) s)) (Imp H (c (Ch SAR s)))))
           (define natS (natline-c ALD s))
           (obt H (list sLD (split-line SAR B s)) (c (split-goal SAR B s))
             (lambda (a Pa H1)
               (obt H1 '() Pa
                 (lambda (bb _ H2)
                   (T (list sR lineLD sLD natS (chuq-line SAR a s) (leib (Add HOLE bb s) a s) (chnat-line B bb) (lu 'AddSelf s bb) (chzero-line B bb))
                      (Imp H2 goal))))))]))
      (define (natline-c lst s) (chnat-line lst s))
      (define final
        (unpack 0 H0 '()
          (lambda (H vals)
            ;; per row: the line H -> Ch(L_i ++ [d_i], r_i)  (and H -> Ch(R_i, r_i) holds by the context)
            (define LD (for/list ([L Ls] [v vals]) (append L (list (caddr v)))))
            (define ld-lines
              (for/list ([L Ls] [v vals])
                (match-define (list l r d) v)
                (if (null? L)
                    (T (list (lu 'AddZL l d) (lu '(Uq add) l d r d)) (Imp H (c (Ch (list d) r))))
                    (T (list (app-line L (list d) l d r) (Y (Eqv d d))) (Imp H (c (Ch (append L (list d)) r)))))))
            (define copies (append* (for/list ([yi y] [i (in-naturals)]) (rep yi i))))
            ;; accumulate: value s with H -> Ch(ALD, s) and H -> Ch(AR, s)
            (define (natline lst s) (if (null? lst) (lu 'NatZero s) (chnat-line lst s)))
            (define (acc H ks s ALD AR lineLD lineR)
              (cond
                [(null? ks) (finish H s ALD AR lineLD lineR)]
                [else
                 (define i (car ks)) (match-define (list l r d) (list-ref vals i))
                 (define LDi (list-ref LD i)) (define Ri (list-ref Rs i))
                 (obt H (list lineLD (natline ALD s) (natline LDi r) (list-ref ld-lines i) (tot-add s r)) (ex-add s r)
                   (lambda (s2 _ H1)
                     (define nLD (T (list lineLD (list-ref ld-lines i) (app-line ALD LDi s r s2)) (Imp H1 (c (Ch (append ALD LDi) s2)))))
                     (define AR2 (append AR Ri))
                     (define nR
                       (cond
                         [(null? Ri) (T (list lineR lineLD (lu '(Zinv add) s r s2) (natline ALD s) (leib `(not ,(Ch AR HOLE)) s2 s)) (Imp H1 (c (Ch AR s2))))]
                         [(null? AR) (T (list lineR (natline Ri r) (lu 'AddZL s r) (lu '(Uq add) s r s2 r) (leib `(not ,(Ch Ri HOLE)) s2 r)) (Imp H1 (c (Ch Ri s2))))]
                         [else (T (list lineR (natline AR s) (natline Ri r) (app-line AR Ri s r s2)) (Imp H1 (c (Ch AR2 s2))))]))
                     (acc H1 (cdr ks) s2 (append ALD LDi) AR2 nLD nR)))]))
            (define i0 (car copies)) (match-define (list l0 r0 d0) (list-ref vals i0))
            (acc H (cdr copies) r0 (list-ref LD i0) (list-ref Rs i0) (list-ref ld-lines i0) (T '() (Imp H (c (Ch (list-ref Rs i0) r0))))))))
      (T (list final) (c stmt))))
  (list (hash-ref stats 'steps 0) info))
