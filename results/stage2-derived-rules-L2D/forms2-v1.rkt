#lang racket/base
;; forms2-v1.rkt -- lane L2D: (FAdd N) and (FScale N) for the linear forms of forms-v2.rkt. Not trusted; checked step by
;; step by core-v1's copy of the checker, then by the judges.
;;   (FAdd N)   z, c, c' in w, Ad(c_j,c'_j,c''_j) for all j, FormV(c,z,v), FormV(c',z,v'), Ad(v,v',v'') -> FormV(c'',z,v'')
;;   (FScale N) y, c, z in w, Mu(y,c_j,c'_j) for all j, FormV(c,z,v), Mu(y,v,v') -> FormV(c',z,v')
(require racket/list racket/match (file "C:/ClaudeOutput/pompetzki/lanes/L2D/core-v1.rkt")
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/nd-v3.rkt")
         (except-in (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel-v6.rkt") ids)
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel2-v2.rkt")
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel3-v4.rkt")
         (only-in (file "C:/ClaudeOutput/pompetzki/lanes/L2D/bin-v6.rkt") closed-lemma lem last-consequent dist-inst
                  pred-in trans-w rw-fwd rw-bwd)
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel4-v5.rkt")
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/forms-v2.rkt"))
(provide (all-defined-out))

;; introduce fresh values one after another: (chain-ex k items f) where each item is (lambda (k) fact-exists),
;; f receives (k vars)
(define (chain-ex k items f)
  (let loop ([k k] [items items] [acc '()])
    (if (null? items) (f k (reverse acc))
        (ex-e k ((car items) k) (lambda (k2 x) (loop k2 (cdr items) (cons x acc)))))))
;; x in w from the existence fact (and (in x 0) R) of add-ex / mul-ex: the hypothesis itself
(define (hyp-in k x) (have k `(in ,x 0)))

(defform FAdd (key)
  (define N (cadr key))
  (define (split vs) (values (take vs N) (take (drop vs N) N) (take (drop vs (* 2 N)) N) (take (drop vs (* 3 N)) N)
                             (list-ref vs (* 4 N)) (list-ref vs (+ 1 (* 4 N))) (list-ref vs (+ 2 (* 4 N)))))
  (closed-lemma key (+ (* 4 N) 3)
    (lambda vs (let-values ([(cs cs1 cs2 zs v v1 v2) (split vs)])
                 (append (ins zs) (ins cs) (ins cs1) (for/list ([a cs] [b cs1] [c cs2]) (Ad a b c))
                         (list (FormV cs zs v) (FormV cs1 zs v1) (Ad v v1 v2)))))
    (lambda vs (let-values ([(cs cs1 cs2 zs v v1 v2) (split vs)]) (FormV cs2 zs v2)))
    (lambda (k . vs)
      (define-values (cs cs1 cs2 zs v v1 v2) (split vs))
      (form-open k cs zs v (have k (FormV cs zs v))
        (lambda (k2 ts ss)
          (form-open k2 cs1 zs v1 (have k2 (FormV cs1 zs v1))
            (lambda (k3 ts1 ss1)
              (define S (sums-of* ts ss v N)) (define S1 (sums-of* ts1 ss1 v1 N))
              (define tw (for/list ([c cs] [z zs] [t ts]) (mul-w k3 c z t)))
              (define tw1 (for/list ([c cs1] [z zs] [t ts1]) (mul-w k3 c z t)))
              (cond
                [(= N 1)
                 (ind-use k3 'KRDist (car zs) (list (car cs) (car cs1) (car cs2) v v1 v2))]
                [else
                 ;; T_j = t_j + t1_j
                 (chain-ex k3 (for/list ([t ts] [t1 ts1] [w tw] [w1 tw1]) (lambda (k) (add-ex k t t1 w w1)))
                   (lambda (k4 Ts)
                     (define mus (for/list ([c cs] [c1 cs1] [c2 cs2] [z zs] [t ts] [t1 ts1] [T Ts])
                                   (ind-use k4 'KRDist z (list c c1 c2 t t1 T))))
                     ;; S_k in w
                     (define Sw (for/list ([kk N]) (if (= kk 0) (car tw) (if (< kk (sub1 N)) (add-w k4 (list-ref S (sub1 kk)) (list-ref ts kk) (list-ref S kk)) #f))))
                     (define S1w (for/list ([kk N]) (if (= kk 0) (car tw1) (if (< kk (sub1 N)) (add-w k4 (list-ref S1 (sub1 kk)) (list-ref ts1 kk) (list-ref S1 kk)) #f))))
                     ;; U_k = S_k + S1_k for k = 1 .. N-2 (index), U_0 = T_0, U_N-1 = v2
                     (chain-ex k4 (for/list ([kk (in-range 1 (sub1 N))]) (lambda (k) (add-ex k (list-ref S kk) (list-ref S1 kk) (list-ref Sw kk) (list-ref S1w kk))))
                       (lambda (k5 Umid)
                         (define U (append (list (car Ts)) Umid (list v2)))
                         (define adds
                           (for/list ([kk (in-range 1 N)])
                             (lem k5 'KX4 (list (list-ref S (sub1 kk)) (list-ref ts kk) (list-ref S1 (sub1 kk)) (list-ref ts1 kk)
                                                (list-ref S kk) (list-ref S1 kk) (list-ref U (sub1 kk)) (list-ref Ts kk) (list-ref U kk))
                                  (list-ref Sw (sub1 kk)) (list-ref tw kk) (list-ref S1w (sub1 kk)) (list-ref tw1 kk))))
                         (form-pack k5 cs2 zs Ts Umid v2 (append mus adds)))))))])))))))

(defform FScale (key)
  (define N (cadr key))
  (define (split vs) (values (car vs) (take (cdr vs) N) (take (drop (cdr vs) N) N) (take (drop (cdr vs) (* 2 N)) N)
                             (list-ref vs (+ 1 (* 3 N))) (list-ref vs (+ 2 (* 3 N)))))
  (closed-lemma key (+ (* 3 N) 3)
    (lambda vs (let-values ([(y cs cs1 zs v v1) (split vs)])
                 (append (list `(in ,y 0)) (ins cs) (ins zs) (for/list ([c cs] [c1 cs1]) (Mu y c c1))
                         (list (FormV cs zs v) (Mu y v v1)))))
    (lambda vs (let-values ([(y cs cs1 zs v v1) (split vs)]) (FormV cs1 zs v1)))
    (lambda (k . vs)
      (define-values (y cs cs1 zs v v1) (split vs))
      (form-open k cs zs v (have k (FormV cs zs v))
        (lambda (k2 ts ss)
          (define S (sums-of* ts ss v N))
          (define tw (for/list ([c cs] [z zs] [t ts]) (mul-w k2 c z t)))
          (cond
            [(= N 1) (ind-use k2 'KMulAs (car zs) (list y (car cs) v v1 (car cs1)))]
            [else
             ;; T_j = y t_j
             (chain-ex k2 (for/list ([t ts] [w tw]) (lambda (k) (mul-ex k y t w)))
               (lambda (k3 Ts)
                 (define mus (for/list ([c cs] [c1 cs1] [z zs] [t ts] [T Ts]) (ind-use k3 'KMulAs z (list y c t T c1))))
                 (define Sw (for/list ([kk N]) (if (= kk 0) (car tw) (if (< kk (sub1 N)) (add-w k3 (list-ref S (sub1 kk)) (list-ref ts kk) (list-ref S kk)) #f))))
                 (define Tw (for/list ([T Ts] [t ts]) (mul-w k3 y t T)))
                 ;; U_k = y S_k for k = 1 .. N-2, U_0 = T_0, U_N-1 = v1
                 (chain-ex k3 (for/list ([kk (in-range 1 (sub1 N))]) (lambda (k) (mul-ex k y (list-ref S kk) (list-ref Sw kk))))
                   (lambda (k4 Umid)
                     (define U (append (list (car Ts)) Umid (list v1)))
                     (define Uw (for/list ([kk (in-range 0 (sub1 N))]) (if (= kk 0) (car Tw) (mul-w k4 y (list-ref S kk) (list-ref U kk)))))
                     ;; Ad(U_k-1, T_k, U_k): y S_k = y S_k-1 + y t_k = R, R = U_k
                     (let loop ([k4 k4] [kk 1] [facts '()])
                       (cond
                         [(= kk N) (form-pack k4 cs1 zs Ts Umid v1 (append mus (reverse facts)))]
                         [else
                          (ex-e k4 (add-ex k4 (list-ref U (sub1 kk)) (list-ref Ts kk) (list-ref Uw (sub1 kk)) (list-ref Tw kk))
                            (lambda (k5 R)
                              (define m1 (dist-inst k5 (list-ref ts kk) y (list-ref S (sub1 kk)) (list-ref S kk) (list-ref U (sub1 kk)) (list-ref Ts kk) R
                                                    (list-ref tw kk) (list-ref Sw (sub1 kk))))   ; Mu(y, S_k, R)
                              (define Skw (if (< kk (sub1 N)) (list-ref Sw kk) (add-w k5 (list-ref S (sub1 kk)) (list-ref ts kk) (list-ref S kk))))
                              (define e1 (mul-uq k5 y (list-ref S kk) R (list-ref U kk) Skw m1))  ; R = U_k
                              (define a1 (rw-fwd k5 (lambda (h) (Ad (list-ref U (sub1 kk)) (list-ref Ts kk) h)) R (list-ref U kk) e1))
                              (loop k5 (add1 kk) (cons a1 facts))))]))))))]))))))

(define (sums-of* ts ss v N) (if (= N 1) (list v) (append (list (car ts)) ss (list v))))
