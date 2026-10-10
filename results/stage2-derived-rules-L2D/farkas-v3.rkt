#lang racket/base
;; farkas-v3.rkt -- farkas-v2.rkt with the closing brackets of the scaling, summing and final branches corrected.
;; farkas-v2.rkt -- lane L2D, derived rule Farkas (second version; v1's exists-elimination continuations returned the
;; wrong values). A certificate y >= 0 (integers) with y^T A = 0 and y^T b < 0 for an integer system A x <= b (m rows,
;; n unknowns) becomes the closed ZF theorem that the system has no rational solution.
;; Not trusted; checked step by step by core-v1's copy of the checker, then by both judges.
;;
;; Encoding: x_j = (u_j - v_j) / w with u_j, v_j, w in omega, w /= 0. Row i, A_i x <= b_i, multiplied by w and with the
;; negative terms moved across, is  L_i(z) + d_i = R_i(z)  for some d_i in omega, z = (u_1..u_n, v_1..v_n, w):
;;   L_i: u_j -> max(a_ij,0), v_j -> max(-a_ij,0), w -> max(-b_i,0);   R_i: u_j -> max(-a_ij,0), v_j -> max(a_ij,0), w -> max(b_i,0)
;; Statement (FormV of forms-v2.rkt; coefficients are numeral variables k with Bin hypotheses, 0 is o):
;;   forall w p g o (Ctx -> forall k_1..k_C (Bin_val1(k_1) -> ... -> forall z_1..z_N (z_1 in w -> ... -> z_N in w ->
;;        not Emp(z_N) -> not (Row_1 & ... & Row_m))))
;;   Row_i = exists l r d ((FormV(Lc_i, z, l) & FormV(Rc_i, z, r)) & (d in w & Ad(l,d,r)))
;; Proof: scale row i by y_i (FScale, distributivity), add the rows (FAdd, KX4); y^T A = 0 makes the totals agree in
;; every coefficient but w's, where the left exceeds the right by delta = -y^T b >= 1; FUnit, FAdd and FFun give
;; Lt = Rt + delta w; with Lt + D = Rt, associativity, commutativity and cancellation give delta w + D = 0, so
;; Emp(delta w) (KZeroSum), against KMulNZ (delta >= 1, w /= 0).
;; Usage: racket farkas-v2.rkt emit CERT.sexp OUT.jdg      CERT: (farkas (A rows) (b vector) (y vector))
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

(define (row-coeffs A b i)
  (define a (list-ref A i)) (define bi (list-ref b i))
  (values (append (for/list ([x a]) (max x 0)) (for/list ([x a]) (max (- x) 0)) (list (max (- bi) 0)))
          (append (for/list ([x a]) (max (- x) 0)) (for/list ([x a]) (max x 0)) (list (max bi 0)))))
(define (Row Lcs Rcs zs)
  (define l (gs 'l)) (define r (gs 'r)) (define d (gs 'd))
  `(ex ,l (ex ,r (ex ,d (and (and ,(FormV Lcs zs l) ,(FormV Rcs zs r)) (and (in ,d 0) ,(Ad l d r)))))))
(define (farkas-H A b cv zs)
  (bconj-dsl (for/list ([i (length A)]) (let-values ([(L R) (row-coeffs A b i)]) (Row (map cv L) (map cv R) zs)))))

(define (farkas-thm! key A b y)
  (define m (length A)) (define n (length (car A))) (define N (+ n n 1))
  (for ([yi y]) (when (< yi 0) (error 'farkas "negative multiplier")))
  (for ([j n]) (unless (= 0 (for/sum ([i m]) (* (list-ref y i) (list-ref (list-ref A i) j)))) (error 'farkas "y^T A /= 0 at column ~a" j)))
  (define ytb (for/sum ([i m]) (* (list-ref y i) (list-ref b i))))
  (unless (< ytb 0) (error 'farkas "y^T b = ~a is not negative" ytb))
  (define vals (sort (remove-duplicates (filter positive? (append (for*/list ([r A] [x r]) (abs x)) (map abs b)))) <))
  (define C (length vals))
  (begin-thm! key (+ 4 C N))
  (define kvars (for/list ([i C]) (+ 4 i)))
  (define zs (for/list ([i N]) (+ 4 C i)))
  (define zN (last zs))
  (define canon (make-hash (cons (cons 0 3) (for/list ([v vals] [x kvars]) (cons v x)))))
  (define (cvar v) (hash-ref canon v))
  (define H (farkas-H A b cvar zs))
  (define binhyps (for/list ([v vals] [x kvars]) (Bin v x)))
  (define kB (apply cx+ (kctx) binhyps))
  (define k0 (apply cx+ kB (append (for/list ([z zs]) `(in ,z 0)) (list `(not (pr Emp ,zN)) H))))
  ;; the values
  (define rowsLR (for/list ([i m]) (let-values ([(L R) (row-coeffs A b i)]) (cons L R))))
  (define act (for/list ([i m] #:when (> (list-ref y i) 0)) i))
  (define (scale yi vec) (map (lambda (c) (* yi c)) vec))
  (define partial
    (let loop ([is act] [accL #f] [accR #f] [out '()])
      (if (null? is) (reverse out)
          (let* ([yi (list-ref y (car is))]
                 [L (if accL (map + accL (scale yi (car (list-ref rowsLR (car is))))) (scale yi (car (list-ref rowsLR (car is)))))]
                 [R (if accR (map + accR (scale yi (cdr (list-ref rowsLR (car is))))) (scale yi (cdr (list-ref rowsLR (car is)))))])
            (loop (cdr is) L R (cons (cons L R) out))))))
  (define KLf (car (last partial))) (define KRf (cdr (last partial)))
  (for ([j (sub1 N)]) (unless (= (list-ref KLf j) (list-ref KRf j)) (error 'farkas "coefficients differ at ~a" j)))
  (define delta (- (last KLf) (last KRf)))
  (unless (= delta (- ytb)) (error 'farkas "delta ~a" delta))
  (define needed (remove-duplicates (filter positive? (append (map (lambda (i) (list-ref y i)) act)
                                                              (append* (for/list ([i act]) (append (scale (list-ref y i) (car (list-ref rowsLR i)))
                                                                                                   (scale (list-ref y i) (cdr (list-ref rowsLR i))))))
                                                              (append* (for/list ([p partial]) (append (car p) (cdr p))))
                                                              (list delta)))))
  (define new-vals (filter (lambda (v) (not (hash-ref canon v #f))) needed))
  ;; ---- the proof of not H in k0
  (define notH
    (chain-ex k0 (for/list ([v new-vals]) (lambda (k) (lemma-fact k `(BinEx ,v))))
      (lambda (k1 nvars)
        (for ([v new-vals] [x nvars]) (hash-set! canon v x))
        (define in-cache (make-hash))
        (define (num-in k v) (hash-ref! in-cache v (lambda () (if (= v 0) (zerow k 3) (lem k `(BinW ,v) (list (cvar v)))))))
        (define zin (for/list ([z zs]) (have k1 `(in ,z 0))))
        (define zNw (last zin))
        (define Hf (have k1 H))
        (define (coef-mu k yv c)                 ; Mu(Y, C, C') for the numerals of y, c, y*c
          (if (= c 0) (mul-z k (cvar yv) (num-in k yv)) (lem k `(CMul ,yv ,c) (list (cvar yv) (cvar c) (cvar (* yv c))))))
        (define (coef-ad k a c)                  ; Ad(A, C, A+C)
          (lem k `(CAdd ,a ,c) (list (cvar a) (cvar c) (cvar (+ a c)))))
        (define (fw k cs v fl) (lem k `(FW ,N) (append (map cvar cs) zs (list v)) fl))
        ;; rows, then scaling, then sums, then the end
        (let rows ([k k1] [i 0] [acc '()])
          (cond
            [(< i m)
             (define L (car (list-ref rowsLR i))) (define R (cdr (list-ref rowsLR i)))
             (ex-e k (have k (Row (map cvar L) (map cvar R) zs) Hf)
               (lambda (k2 l)
                 (ex-e k2 (have k2 (last (cx-hyps k2)))
                   (lambda (k3 r)
                     (ex-e k3 (have k3 (last (cx-hyps k3)))
                       (lambda (k4 d)
                         (define fl (have k4 (FormV (map cvar L) zs l)))
                         (define fr (have k4 (FormV (map cvar R) zs r)))
                         (define din (have k4 `(in ,d 0)))
                         (define ad (have k4 (Ad l d r)))
                         (rows k4 (add1 i) (cons (list i l r d fl fr din ad) acc))))))))]
            [else
             (define rws (reverse acc))
             ;; scaling of the active rows
             (let scl ([k k] [is act] [out '()])
               (cond
                 [(pair? is)
                  (match-define (list i l r d fl fr din ad) (list-ref rws (car is)))
                  (define yi (list-ref y i))
                  (define L (car (list-ref rowsLR i))) (define R (cdr (list-ref rowsLR i)))
                  (define Y (cvar yi)) (define Yw (num-in k yi))
                  (define lw (fw k L l fl)) (define rw (fw k R r fr))
                  (ex-e k (mul-ex k Y l Yw lw)
                    (lambda (k2 l2)
                      (ex-e k2 (mul-ex k2 Y r Yw rw)
                        (lambda (k3 r2)
                          (ex-e k3 (mul-ex k3 Y d Yw din)
                            (lambda (k4 d2)
                              (define (scale-form cs cs2 v v2 f)
                                (lem k4 `(FScale ,N) (append (list Y) (map cvar cs) (map cvar cs2) zs (list v v2))
                                     Yw (map (lambda (c) (num-in k4 c)) cs) zin (map (lambda (c) (coef-mu k4 yi c)) cs) f))
                              (define fl2 (scale-form L (scale yi L) l l2 fl))
                              (define fr2 (scale-form R (scale yi R) r r2 fr))
                              (define l2w (mul-w k4 Y l l2)) (define d2w (mul-w k4 Y d d2))
                              (ex-e k4 (add-ex k4 l2 d2 l2w d2w)
                                (lambda (k5 R5)
                                  (define m1 (dist-inst k5 d Y l r l2 d2 R5 din Yw lw ad))      ; Mu(Y, r, R5)
                                  (define e1 (mul-uq k5 Y r r2 R5 rw m1))                       ; r2 = R5
                                  (define ad2 (rw-bwd k5 (lambda (h) (Ad l2 d2 h)) r2 R5 e1))     ; Ad(l2,d2,r2)
                                  (scl k5 (cdr is) (cons (list i l2 r2 d2 fl2 fr2 ad2 (scale yi L) (scale yi R) l2w d2w) out))))))))))]
                 [else
                  (define srs (reverse out))
                  ;; sums
                  (match-define (list _ l1 r1 d1 fl1 fr1 ad1 cL1 cR1 l1w d1w) (car srs))
                  (let sm ([k k] [rest (cdr srs)] [Lt l1] [Rt r1] [Dt d1] [fL fl1] [fR fr1] [adt ad1] [cL cL1] [cR cR1] [Dtw d1w])
                    (cond
                      [(pair? rest)
                       (match-define (list _ l2 r2 d2 fl2 fr2 ad2 cL2 cR2 l2w d2w) (car rest))
                       (define Ltw (fw k cL Lt fL)) (define Rtw (fw k cR Rt fR))
                       (define r2w (fw k cR2 r2 fr2))
                       (ex-e k (add-ex k Lt l2 Ltw l2w)
                         (lambda (k2 Lt2)
                           (ex-e k2 (add-ex k2 Rt r2 Rtw r2w)
                             (lambda (k3 Rt2)
                               (ex-e k3 (add-ex k3 Dt d2 Dtw d2w)
                                 (lambda (k4 Dt2)
                                   (define cLn (map + cL cL2)) (define cRn (map + cR cR2))
                                   (define (add-form cs cs2 cs3 v v2 v3 f1 f2)
                                     (lem k4 `(FAdd ,N) (append (map cvar cs) (map cvar cs2) (map cvar cs3) zs (list v v2 v3))
                                          zin (map (lambda (c) (num-in k4 c)) cs) (map (lambda (c) (num-in k4 c)) cs2)
                                          (map (lambda (a c) (coef-ad k4 a c)) cs cs2) f1 f2))
                                   (define fL3 (add-form cL cL2 cLn Lt l2 Lt2 fL fl2))
                                   (define fR3 (add-form cR cR2 cRn Rt r2 Rt2 fR fr2))
                                   (define ad3 (lem k4 'KX4 (list Lt Dt l2 d2 Rt r2 Lt2 Dt2 Rt2) Ltw Dtw l2w d2w adt ad2))
                                   (define Dt2w (add-w k4 Dt d2 Dt2))
                                   (sm k4 (cdr rest) Lt2 Rt2 Dt2 fL3 fR3 ad3 cLn cRn Dt2w)))))))]
                      [else
                       ;; the end: Lt = Rt + delta w, Lt + Dt = Rt
                       (define D (cvar delta)) (define Dw (num-in k delta))
                       (define Rtw (fw k cR Rt fR))
                       (ex-e k (mul-ex k D zN Dw zNw)
                         (lambda (k2 E)
                           (define Ew (mul-w k2 D zN E))
                           (define unit-cs (append (make-list (sub1 N) 0) (list delta)))
                           (define fu (lem k2 `(FUnit ,N ,(sub1 N)) (append (list D) zs (list E)) zin Dw))
                           (ex-e k2 (add-ex k2 Rt E Rtw Ew)
                             (lambda (k3 X)
                               (define coefs (for/list ([a cR] [c unit-cs] [t cL])
                                               (if (= c 0) (add-z k3 (cvar a) (num-in k3 a)) (coef-ad k3 a c))))
                               (define fX (lem k3 `(FAdd ,N) (append (map cvar cR) (map cvar unit-cs) (map cvar cL) zs (list Rt E X))
                                               zin (map (lambda (c) (num-in k3 c)) cR) (map (lambda (c) (num-in k3 c)) unit-cs) coefs fR fu))
                               (define xl (lem k3 `(FFun ,N) (append (map cvar cL) zs (list X Lt)) zin fX fL))   ; X = Lt
                               (define a1 (rw-fwd k3 (lambda (h) (Ad Rt E h)) X Lt xl))                           ; Ad(Rt,E,Lt)
                               (ex-e k3 (add-ex k3 E Dt Ew Dtw)
                                 (lambda (k4 Q)
                                   (define Qw (add-w k4 E Dt Q))
                                   (define a2 (add-assoc k4 Rt E Dt Lt Rt Q Dtw Rtw Ew a1 adt))          ; Ad(Rt,Q,Rt)
                                   (define a3 (add-comm k4 Rt Q Rt Rtw Qw a2))                            ; Ad(Q,Rt,Rt)
                                   (define a4 (l0 k4 Rt Rtw))                                             ; Ad(o,Rt,Rt)
                                   (define q0 (cancel k4 Rt Q 3 Rt Rtw Qw (zerow k4 3) a3 a4))            ; Q = o
                                   (define a5 (rw-fwd k4 (lambda (h) (Ad E Dt h)) Q 3 q0))                 ; Ad(E,Dt,o)
                                   (define em (zero-sum k4 E Dt Ew Dtw a5))                               ; Emp(E)
                                   (ex-e k4 (lem k4 `(BinPos ,delta) (list D))
                                     (lambda (k5 kk)
                                       (define kkw (trans-w k5 kk D Dw (pred-in k5 D kk)))
                                       (define nem (lem k5 'KMulNZ (list D kk zN E) kkw zNw))
                                       (have k5 `(not ,H) em nem)))))))))]))]))])))))
  ;; ---- closing
  (define f1 (have kB `(imp ,@(for/list ([z zs]) `(in ,z 0)) (not (pr Emp ,zN)) (not ,H)) notH))
  (define f2 (for/fold ([cur f1]) ([z (reverse zs)]) (all-i kB z cur)))
  (define f3 (have (kctx) `(imp ,@binhyps ,(concl kB f2)) f2))
  (define f4 (for/fold ([cur f3]) ([x (reverse kvars)]) (all-i (kctx) x cur)))
  (define g (for/fold ([cur f4]) ([v '(3 2 1 0)]) (G cur v)))
  (end-thm! (line g) '()))

;; ------------------------------------------------------------------ files
(define (emit-file cert-path out)
  (load-base!)
  (reset-batch!)
  (match-define (list 'farkas (list 'A A) (list 'b b) (list 'y y)) (call-with-input-file cert-path read))
  (define key `(Farkas ,(path->string (file-name-from-path cert-path))))
  (define t0 (current-milliseconds))
  (farkas-thm! key A b y)
  (define ms (- (current-milliseconds) t0))
  (define text (batch-text))
  (write-new out text)
  (define-values (rg ths) (read-jdg-text text))
  (define base (regexp-replace #rx"[.]jdg$" out ""))
  (define mdir (string-append base "-mut"))
  (make-directory* mdir)
  (define pflags (map caddr (reverse out-thms)))
  (define keys (map car (reverse out-thms)))
  ;; twin: the statement for the system without its last row (a different statement)
  (define stmt (tof (car (last ths))))
  (define twin (Neg stmt))
  (define tv (list->vector ths))
  (define last-i (sub1 (vector-length tv)))
  (match-define (list lst lsig lsteps lhyps) (vector-ref tv last-i))
  (define Ts (for/list ([s lsteps] [i (in-naturals)] #:when (eq? (car s) 'T)) i))
  (define (with-step k f)
    (structure-text rg (for/list ([x tv] [j (in-naturals)])
                         (if (= j last-i) (list lst lsig (for/list ([s lsteps] [i (in-naturals)]) (if (= i k) (f s) s)) lhyps) x))))
  (define targeted
    (list (list "main-last-taut-neg" (with-step (last Ts) (match-lambda [(list 'T ls g) (list 'T ls (list 'n g))])))
          (list "main-mid-taut-drop" (with-step (list-ref Ts (quotient (length Ts) 2)) (match-lambda [(list 'T ls g) (list 'T (if (null? ls) ls (cdr ls)) g)])))))
  (define muts (append targeted (mutants text twin pflags)))
  (define lines
    (list (format "~a  from ~a: A = ~a, b = ~a, y = ~a" out cert-path A b y)
          (format "  theorems ~a (prelude ~a, generated ~a), steps ~a (prelude ~a; main theorem ~a), bytes ~a, build ~a ms"
                  (length ths) (hash-ref stats 'prelude 0) (hash-ref stats 'theorems 0)
                  (+ (hash-ref stats 'steps 0) (hash-ref stats 'prelude-steps 0)) (hash-ref stats 'prelude-steps 0) (length lsteps)
                  (file-size out) ms)
          (format "  largest tautology test ~a calls" (hash-ref stats 'taut-max 0))
          (format "  sha256 ~a" (sha256-hex out))
          (format "  registry: ~a" (check-registry-text text))
          (format "  copy of the checker: ~a" (check-batch rg ths))))
  (for-each displayln lines)
  (define mlines
    (for/list ([mu muts])
      (match-define (list tag mtext) mu)
      (define mf (build-path mdir (string-append (path->string (file-name-from-path base)) "-" tag ".jdg")))
      (write-new mf mtext)
      (define-values (mrg mths) (read-jdg-text mtext))
      (format "  mutant ~a: copy of the checker ~a" tag (check-batch mrg mths))))
  (for-each displayln mlines)
  (write-new (string-append base ".index.txt") (string-join (for/list ([k keys] [i (in-naturals)]) (format "~a ~s" i k)) "\n"))
  (write-new (string-append base ".manifest.txt") (string-join (append lines mlines) "\n")))

(module+ main
  (define args (vector->list (current-command-line-arguments)))
  (match args
    [(list "emit" cert out) (emit-file cert out)]
    [_ (printf "usage: racket farkas-v2.rkt emit CERT.sexp OUT.jdg\n")]))
