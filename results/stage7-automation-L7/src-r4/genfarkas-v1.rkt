#lang racket/base
;; genfarkas-v1.rkt -- lane L7 round 2: Farkas certificates for the L7 emitter, in L2D's format (farkas (A ..) (b ..) (y ..)).
;;  - L2D's four inputs (lanes\L2D\farkas\in\f1-1d .. f4-2d), read only;
;;  - cyclic chains: x1 - x2 <= -1, ..., xk - x1 <= -1 (y = all ones, y^T b = -k);
;;  - planted systems (exact LCG): rows 1..m-1 random in [-2,2], y random in [1,2], the last row = -(sum of y_i A_i) so that
;;    y^T A = 0, and b chosen so that y^T b = -delta with delta in {1,2};
;;  - G2's corpus when lanes\G2-farkas\INDEX.tsv exists (read only; only certificates in L2D's format).
;; The certificate check here is the emitter's own; both judges check the derivations.
(require racket/list racket/match racket/file racket/string)
(provide (all-defined-out))

(define (cert-ok? A b y)
  (define m (length A)) (define n (length (car A)))
  (and (= (length b) m) (= (length y) m) (andmap (lambda (v) (and (exact-integer? v) (>= v 0))) y)
       (for/and ([j n]) (= 0 (for/sum ([i m]) (* (list-ref y i) (list-ref (list-ref A i) j)))))
       (< (for/sum ([i m]) (* (list-ref y i) (list-ref b i))) 0)))
;; the length of the left chain of the derivation: sum of y_i (|L_i| + 1), |L_i| = sum of 2... in the encoding:
;; L_i has a_ij+ copies of u_j, a_ij- copies of v_j, b_i- copies of w
(define (left-width A b y)
  (for/sum ([row A] [bi b] [yi y]) (* yi (+ 1 (for/sum ([x row]) (abs x)) (max 0 (- bi))))))
(define (right-width A b y)
  (for/sum ([row A] [bi b] [yi y]) (* yi (+ (for/sum ([x row]) (abs x)) (max 0 bi)))))

(define (l2d-certs)
  (for/list ([f '("f1-1d" "f2-2d" "f3-2d" "f4-2d")])
    (match-define (list 'farkas (list 'A A) (list 'b b) (list 'y y))
      (call-with-input-file (format "C:/ClaudeOutput/pompetzki/lanes/L2D/farkas/in/~a.sexp" f) read))
    (list (string-append "L2D-" f) A b y)))
(define (cyclic k)
  (define A (for/list ([i k]) (for/list ([j k]) (cond [(= j i) 1] [(= j (modulo (add1 i) k)) -1] [else 0]))))
  (list (format "cyclic-~a" k) A (rep-list k -1) (rep-list k 1)))
(define (rep-list k x) (for/list ([i k]) x))

(define g-lcg 20261009)
(define (grand k)
  (set! g-lcg (modulo (+ (* g-lcg 6364136223846793005) 1442695040888963407) 18446744073709551616))
  (modulo (arithmetic-shift g-lcg -33) k))
(define (planted idx n m)
  (define y (for/list ([i m]) (add1 (grand 2))))
  (define rows (for/list ([i (sub1 m)]) (for/list ([j n]) (- (grand 5) 2))))
  (define ym (last y))
  ;; the last row: -(sum_{i<m} y_i A_i) / y_m must be integral; take y_m = 1
  (define y2 (append (drop-right y 1) (list 1)))
  (define last-row (for/list ([j n]) (- (for/sum ([r rows] [yi y2]) (* yi (list-ref r j))))))
  (define A (append rows (list last-row)))
  (define bs (for/list ([i (sub1 m)]) (- (grand 7) 3)))
  (define delta (add1 (grand 2)))
  (define b (append bs (list (- (- (for/sum ([bi bs] [yi y2]) (* yi bi))) delta))))
  (list (format "planted-~a-n~a-m~a" idx n m) A b y2))

;; G2's certificates: INDEX.tsv rows whose certificate file holds (farkas (A ..) (b ..) (y ..)) with integer y
(define G2 "C:/ClaudeOutput/pompetzki/lanes/G2-farkas")
(define (g2-certs)
  (define idx (build-path G2 "INDEX.tsv"))
  (cond
    [(not (file-exists? idx)) '()]
    [else
     (filter values
       (for/list ([ln (cdr (file->lines idx))])
         (define cols (string-split ln "\t"))
         (define path (for/first ([x cols] #:when (regexp-match? #rx"[.](sexp|rktd|txt)$" x)) x))
         (define full (and path (if (absolute-path? path) path (path->string (build-path G2 path)))))
         (with-handlers ([exn:fail? (lambda (e) #f)])
           (and full (file-exists? full)
                (match (call-with-input-file full read)
                  [(list 'farkas (list 'A A) (list 'b b) (list 'y y))
                   (and (andmap exact-integer? y) (andmap (lambda (r) (andmap exact-integer? r)) A) (andmap exact-integer? b)
                        (list (string-append "G2-" (car cols)) A b y))]
                  [_ #f])))))]))
