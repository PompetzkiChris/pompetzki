#lang racket/base
;; forms-v1.rkt -- lane L2D: linear forms over omega with symbolic coefficients, for the Farkas emitter.
;; Not trusted; checked step by step by core-v1's copy of the checker, then by the judges.
;;   FormV_N(c_1..c_N, z_1..z_N, v):  v = c_1 z_1 + ... + c_N z_N, the sum nested to the left:
;;     N = 1: Mu(c_1,z_1,v);  N >= 2: exists t_1..t_N s_2..s_N-1 (Mu(c_j,z_j,t_j) ... & Ad(t_1,t_2,s_2) & ... &
;;     Ad(s_N-1,t_N,v))   (conjunction as a balanced tree)
;; Lemmas, one per N (and position j), statements Ctx -> forall ...:
;;   (FFun N)    z in w, FormV(c,z,v), FormV(c,z,v') -> v = v'
;;   (FAdd N)    z, c, c' in w, Ad(c_j,c'_j,c''_j) for all j, FormV(c,z,v), FormV(c',z,v'), Ad(v,v',v'') -> FormV(c'',z,v'')
;;   (FScale N)  y, z, c in w, Mu(y,c_j,c'_j) for all j, FormV(c,z,v), Mu(y,v,v') -> FormV(c',z,v')
;;   (FUnit N j) z in w, c in w, Mu(c,z_j,t) -> FormV(o,..,c,..,o; z; t)      (c at position j)
(require racket/list racket/match (file "C:/ClaudeOutput/pompetzki/lanes/L2D/core-v1.rkt")
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/nd-v3.rkt")
         (except-in (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel-v6.rkt") ids)
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel2-v2.rkt")
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel3-v4.rkt")
         (only-in (file "C:/ClaudeOutput/pompetzki/lanes/L2D/bin-v6.rkt") closed-lemma lem last-consequent dist-inst
                  pred-in trans-w rw-fwd rw-bwd)
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel4-v5.rkt"))
(provide (all-defined-out))

(define (bconj-dsl xs) (if (null? (cdr xs)) (car xs) (let-values ([(l r) (split-at xs (quotient (length xs) 2))]) `(and ,(bconj-dsl l) ,(bconj-dsl r)))))
;; the parts of FormV: (values term-names sum-names relations) for given term/sum variables
(define (form-rels cs zs ts ss v)
  (define N (length cs))
  (define sums (append (list (car ts)) ss (list v)))           ; s_1 = t_1, s_2 .. s_N-1, s_N = v
  (append (for/list ([c cs] [z zs] [t ts]) (Mu c z t))
          (for/list ([k (in-range 1 N)]) (Ad (list-ref sums (sub1 k)) (list-ref ts k) (list-ref sums k)))))
(define (FormV cs zs v)
  (define N (length cs))
  (cond [(= N 1) (Mu (car cs) (car zs) v)]
        [else
         (define ts (for/list ([i N]) (gs 't)))
         (define ss (for/list ([i (- N 2)]) (gs 's)))
         `(ex ,@ts ,@ss ,(bconj-dsl (form-rels cs zs ts ss v)))]))
;; unpack FormV (fact l) for N >= 2: body gets (k2 ts ss) with the relations as facts of k2
(define (form-open k cs zs v l body)
  (define N (length cs))
  (cond
    [(= N 1) (body k (list v) '())]
    [else
     (let loop ([k k] [l l] [vars '()] [left (+ N (- N 2))])
       (if (= left 0)
           (let ([vs (reverse vars)]) (body k (take vs N) (drop vs N)))
           (ex-e k l (lambda (k2 x) (loop k2 (have k2 (last (cx-hyps k2))) (cons x vars) (sub1 left))))))]))
;; pack FormV from facts of its relations (ls)
(define (form-pack k cs zs ts ss v ls)
  (define N (length cs))
  (cond
    [(= N 1) (have k (Mu (car cs) (car zs) v) ls)]
    [else
     (define names (append (for/list ([i N]) (gs 't)) (for/list ([i (- N 2)]) (gs 's))))
     (define actual (append ts ss))
     (define body (have k (bconj-dsl (form-rels cs zs ts ss v)) ls))
     ;; exists-intro from the innermost variable outwards
     (for/fold ([cur body]) ([i (in-range (length names) 0 -1)])
       (define here (list-ref names (sub1 i)))
       (define bound (drop names i))
       (define sub (for/list ([n names] [a actual] [j (in-naturals)]) (if (>= j (sub1 i)) n a)))
       (define rels (form-rels cs zs (take sub N) (drop sub N) v))
       (define X (if (null? bound) `(ex ,here ,(bconj-dsl rels)) `(ex ,here (ex ,@bound ,(bconj-dsl rels)))))
       (ex-i k cur (list-ref actual (sub1 i)) X))]))
(define (sums-of ts ss v) (append (list (car ts)) ss (list v)))

(define-syntax-rule (defform name (key) body ...) (hash-set! generators 'name (lambda (key) body ...)))
(define (ins zs) (for/list ([z zs]) `(in ,z 0)))

;; ------------------------------------------------------------------ FFun
(defform FFun (key)
  (define N (cadr key))
  (closed-lemma key (+ N N 2)
    (lambda vs (let ([cs (take vs N)] [zs (take (drop vs N) N)] [v (list-ref vs (* 2 N))] [v2 (list-ref vs (add1 (* 2 N)))])
                 (append (ins zs) (list (FormV cs zs v) (FormV cs zs v2)))))
    (lambda vs `(eq ,(list-ref vs (* 2 N)) ,(list-ref vs (add1 (* 2 N)))))
    (lambda (k . vs)
      (define cs (take vs N)) (define zs (take (drop vs N) N)) (define v (list-ref vs (* 2 N))) (define v2 (list-ref vs (add1 (* 2 N))))
      (form-open k cs zs v (have k (FormV cs zs v))
        (lambda (k2 ts ss)
          (form-open k2 cs zs v2 (have k2 (FormV cs zs v2))
            (lambda (k3 ts2 ss2)
              (cond
                [(= N 1) (mul-uq k3 (car cs) (car zs) v v2)]
                [else
                 ;; t_j = t2_j, then the sums
                 (define teq (for/list ([c cs] [z zs] [t ts] [t2 ts2]) (mul-uq k3 c z t t2)))
                 (define tw (for/list ([c cs] [z zs] [t ts]) (mul-w k3 c z t)))
                 (define S (sums-of ts ss v)) (define S2 (sums-of ts2 ss2 v2))
                 (for/fold ([prev (car teq)]) ([k (in-range 1 N)])      ; prev: S_k-1 = S2_k-1
                   (define a1 (have k3 (Ad (list-ref S2 (sub1 k)) (list-ref ts2 k) (list-ref S2 k))))
                   (define a2 (rw-bwd k3 (lambda (h) (Ad h (list-ref ts2 k) (list-ref S2 k))) (list-ref S (sub1 k)) (list-ref S2 (sub1 k)) prev a1))
                   (define a3 (rw-bwd k3 (lambda (h) (Ad (list-ref S (sub1 k)) h (list-ref S2 k))) (list-ref ts k) (list-ref ts2 k) (list-ref teq k) a2))
                   (add-uq k3 (list-ref S (sub1 k)) (list-ref ts k) (list-ref S k) (list-ref S2 k) (list-ref tw k) a3))])))))))))

;; ------------------------------------------------------------------ FUnit
(defform FUnit (key)
  (match-define (list _ N j) key)                     ; j from 0
  (closed-lemma key (+ N 2)
    (lambda vs (let ([c (car vs)] [zs (take (cdr vs) N)] [t (list-ref vs (add1 N))])
                 (append (ins zs) (list `(in ,c 0) (Mu c (list-ref zs j) t)))))
    (lambda vs (let ([c (car vs)] [zs (take (cdr vs) N)] [t (list-ref vs (add1 N))])
                 (FormV (for/list ([i N]) (if (= i j) c 3)) zs t)))
    (lambda (k . vs)
      (define c (car vs)) (define zs (take (cdr vs) N)) (define t (list-ref vs (add1 N)))
      (define cs (for/list ([i N]) (if (= i j) c 3)))
      (define ow (zerow k 3))
      (define tw (mul-w k c (list-ref zs j) t))
      (define ts (for/list ([i N]) (if (= i j) t 3)))
      (define tfacts (for/list ([i N] [z zs] #:unless (= i j)) (mul0l k z)))
      ;; partial sums: o before j, t from j on; s_2 .. s_N-1 as variables
      (define S (for/list ([kk N]) (if (< kk j) 3 t)))
      (define sfacts
        (for/list ([kk (in-range 1 N)])
          (define prev (list-ref S (sub1 kk))) (define tk (list-ref ts kk)) (define sk (list-ref S kk))
          (cond [(and (= prev 3) (= tk 3)) (add-z k 3 ow)]                       ; o + o = o
                [(= prev 3) (l0 k t tw)]                                          ; o + t = t
                [else (add-z k t tw)])))                                          ; t + o = t
      (form-pack k cs zs ts (if (> N 2) (take (drop S 1) (- N 2)) '()) t (append tfacts sfacts)))))
