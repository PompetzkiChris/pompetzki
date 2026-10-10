#lang racket/base
;; bin-v1.rkt -- lane L2D: binary numerals over the arithmetic kernel (kernel-v6, kernel2-v2, kernel3-v4).
;; Not trusted; every lemma is checked by core-v1's copy of the checker as it is built, then by the judges.
;;
;; Encoding of integers (frame variables 0..3 = w, p, g, o under Ctx, as in the kernel):
;;   Bin_0(x) := Emp(x)          Bin_1(x) := Suc(x,o)
;;   Bin_2m(x)   := exists y (Bin_m(y) & Ad(y,y,x))                              m >= 1
;;   Bin_2m+1(x) := exists y (Bin_m(y) & exists t (Ad(y,y,t) & Suc(x,t)))       m >= 1
;; One existential per bit: the formula has about 5 levels per bit, so a numeral of 30 bits nests about 150 levels
;; (the pmp judge allows about 240). Lemmas, generated per number and cached by key:
;;   (BinW n)  Ctx -> forall x (Bin_n(x) -> x in w)
;;   (BinEx n) Ctx -> exists x Bin_n(x)
;;   (BinUq n) Ctx -> forall x x' (Bin_n(x) -> Bin_n(x') -> x = x')
;;   (BinInc n) Ctx -> forall x s (Bin_n(x) -> Suc(s,x) -> Bin_n+1(s))
;;   (BinAdd a b) Ctx -> forall x y z (Bin_a(x) -> Bin_b(y) -> Ad(x,y,z) -> Bin_a+b(z))
;;   (BinMul a b) Ctx -> forall x y z (Bin_a(x) -> Bin_b(y) -> Mu(x,y,z) -> Bin_ab(z))      a >= 1
;;   (BinPos n) Ctx -> forall x (Bin_n(x) -> exists k Suc(x,k))                            n >= 1
;;   (CMul a b) (CAdd a b) Ctx -> forall x y z (Bin_a(x) -> Bin_b(y) -> Bin_c(z) -> Op(x,y,z)),  c = a*b, a+b
;;   (CNZ n)   Ctx -> forall x (Bin_n(x) -> not Emp(x))                                     n >= 1
;; General lemma KLA (interchange): Ctx -> forall a b A B s S (a,b in w -> Ad(a,a,A) -> Ad(b,b,B) -> Ad(a,b,s) ->
;;   Ad(s,s,S) -> Ad(A,B,S)).
;; Derivation length: BinAdd(a,b) uses O(bits) lemmas, BinMul(a,b) O(bits(b)) BinMul and BinAdd lemmas: O(bits^2).
(require racket/list racket/match (file "C:/ClaudeOutput/pompetzki/lanes/L2D/core-v1.rkt")
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/nd-v3.rkt")
         (except-in (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel-v6.rkt") ids)
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel2-v2.rkt")
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel3-v4.rkt"))
(provide (all-defined-out))

(define (Bin n x)
  (cond [(= n 0) `(pr Emp ,x)]
        [(= n 1) `(pr Suc ,x 3)]
        [else
         (define m (quotient n 2))
         (define y (gs 'y))
         (if (even? n)
             `(ex ,y (and ,(Bin m y) ,(Ad y y x)))
             (let ([t (gs 't)]) `(ex ,y (and ,(Bin m y) (ex ,t (and ,(Ad y y t) (pr Suc ,x ,t)))))))]))

;; a lemma statement  Ctx -> forall v1..vk BODY(v1..vk); proved in context k0 = kctx with fresh variables
(define (closed-lemma key nv hyps con body)
  (begin-thm! key 4)
  (define k (kctx))
  (define names (for/list ([i nv]) (gs 'v)))
  (define goal `(all ,@names (imp ,@(apply hyps names) ,(apply con names))))
  (define goal1 (if (= nv 0) (apply con '()) goal))
  (define r (if (= nv 0)
                (body k)
                (close-all k nv hyps con body goal)))
  (end-thm! (ac `(imp ,CTX-DSL ,goal1)) (ids 4)))
;; use a closed lemma: the instance for frame variables vs, as a fact in k (its hypotheses must follow in k)
(define (lem k key vs . ls)
  (define f (lemma-fact k key))
  (define c0 (concl k f))
  (if (null? vs) f
      (let* ([inst (all-e k f . vs)]) (have k (strip-imps (concl k inst) ls k) inst ls))))
;; the final conclusion of a chain of implications whose premises are given (we return the last consequent)
(define (strip-imps f ls k) (match f [(list 'I _ b) (strip-imps b ls k)] [_ f]))

;; unfold Bin_n(x) proved by fact l: for n >= 2, body receives (k2 y t) with facts for Bin_m(y), Ad(y,y,X) where X = x
;; (even) or t (odd, with Suc(x,t)); t = #f for even n
(define (bin-open k n x l body)
  (define m (quotient n 2))
  (ex-e k l
    (lambda (k2 y)
      (if (even? n)
          (body k2 y #f)
          (ex-e k2 (have k2 `(ex tt (and ,(Ad y y 'tt) (pr Suc ,x tt))))
                (lambda (k3 t) (body k3 y t)))))))
;; pack Bin_n(x) from facts: Bin_m(y) and Ad(y,y,x) (even) or Ad(y,y,t), Suc(x,t) (odd)
(define (bin-pack k n x y t . ls)
  (define m (quotient n 2))
  (cond
    [(even? n) (ex-i k (have k `(and ,(Bin m y) ,(Ad y y x)) ls) y (Bin n x))]
    [else
     (define inner (ex-i k (have k `(and ,(Ad y y t) (pr Suc ,x ,t)) ls) t `(ex tt (and ,(Ad y y 'tt) (pr Suc ,x tt)))))
     (ex-i k (have k `(and ,(Bin m y) (ex tt (and ,(Ad y y 'tt) (pr Suc ,x tt)))) inner ls) y (Bin n x))]))

(define-syntax-rule (defbin name (key) body ...) (hash-set! generators 'name (lambda (key) body ...)))

;; ------------------------------------------------------------------ KLA, the interchange law
;; (a+a)+(b+b) = (a+b)+(a+b):  A + B = A + B... proof: A + B = a + (a + B) [assoc], a + B = (a+b)+b = s + b [assoc],
;; S = s + s = a + (b + s) [assoc], b + s = s + b [comm]
(defkey KLA (key)
  (closed-lemma key 6
    (lambda (a b A B s S) (list `(in ,a 0) `(in ,b 0) (Ad a a A) (Ad b b B) (Ad a b s) (Ad s s S)))
    (lambda (a b A B s S) (Ad A B S))
    (lambda (k a b A B s S)
      (define Aw (add-w k a a A)) (define Bw (add-w k b b B)) (define sw (add-w k a b s))
      ;; q := a + B ; then A + B = a + q  i.e.  (a + a) + B = a + (a + B)   [assoc with x=a y=a z=B u=A s=q]
      (ex-e k (add-ex k a B Bw)
        (lambda (k2 q)
          (ex-e k2 (add-ex k2 A B Aw Bw)
            (lambda (k3 v)
              (define aqv (add-assoc k3 a a B A v q Bw))                      ; Ad(a,q,v)
              ;; q = s + b:  (a + b) + b = a + (b + b) -> Ad(a,B,r) with r = s + b
              (ex-e k3 (add-ex k3 s b sw)
                (lambda (k4 r)
                  (define aBr (add-assoc k4 a b b s r B))                     ; Ad(a,B,r)
                  (define qr (add-uq k4 a B q r Bw aBr))                       ; q = r
                  ;; S = s + s = a + (b + s): assoc with x=a y=b z=s u=s v=S s=bs
                  (ex-e k4 (add-ex k4 b s sw)
                    (lambda (k5 bs)
                      (define aBS (add-assoc k5 a b s s S bs sw))              ; Ad(a,bs,S)
                      (define sbbs (add-comm k5 b s bs sw))                    ; Ad(s,b,bs)
                      (define rbs (add-uq k5 s b r bs sw sbbs))                ; r = bs
                      ;; a + q = v and q = r = bs, a + bs = S  ->  v = S
                      (define aq2 (have k5 (Ad a bs v) aqv qr rbs (leibF (Ad a LHOLE v) q r) (leibF (Ad a LHOLE v) r bs)))
                      (define bsw (add-w k5 b s bs))
                      (define vS (add-uq k5 a bs v S bsw aq2 aBS))
                      (have k5 (Ad A B S) vS (leibF (Ad A B LHOLE) v S)))))))))))))

;; ------------------------------------------------------------------ BinW, BinEx, BinUq, BinPos
(defbin BinW (key)
  (define n (cadr key))
  (closed-lemma key 1 (lambda (x) (list (Bin n x))) (lambda (x) `(in ,x 0))
    (lambda (k x)
      (cond [(= n 0) (zerow k x)]
            [(= n 1) (sucw k 3 x (zerow k 3))]
            [else
             (bin-open k n x (have k (Bin n x))
               (lambda (k2 y t)
                 (define yw (lem k2 `(BinW ,(quotient n 2)) (list y)))
                 (if t
                     (sucw k2 t x (add-w k2 y y t))
                     (add-w k2 y y x))))]))))

(defbin BinEx (key)
  (define n (cadr key))
  (closed-lemma key 0 #f (lambda () `(ex xx ,(Bin n 'xx)))
    (lambda (k)
      (define goal `(ex xx ,(Bin n 'xx)))
      (cond [(= n 0) (ex-i k (have k `(pr Emp 3)) 3 goal)]
            [(= n 1) (ex-e k (suc-ex k 3) (lambda (k2 s) (ex-i k2 (have k2 `(pr Suc ,s 3)) s goal)))]
            [else
             (define m (quotient n 2))
             (ex-e k (lemma-fact k `(BinEx ,m))
               (lambda (k2 y)
                 (define yw (lem k2 `(BinW ,m) (list y)))
                 (ex-e k2 (add-ex k2 y y yw yw)
                   (lambda (k3 t)
                     (if (even? n)
                         (ex-i k3 (bin-pack k3 n t y #f) t goal)
                         (ex-e k3 (suc-ex k3 t)
                           (lambda (k4 s) (ex-i k4 (bin-pack k4 n s y t) s goal))))))))]))))

(defbin BinUq (key)
  (define n (cadr key))
  (closed-lemma key 2 (lambda (x x2) (list (Bin n x) (Bin n x2))) (lambda (x x2) `(eq ,x ,x2))
    (lambda (k x x2)
      (cond [(= n 0) (emp-uq k x x2)]
            [(= n 1) (suc-uq k x x2 3)]
            [else
             (define m (quotient n 2))
             (bin-open k n x (have k (Bin n x))
               (lambda (k2 y t)
                 (bin-open k2 n x2 (have k2 (Bin n x2))
                   (lambda (k3 y2 t2)
                     (define yy (lem k3 `(BinUq ,m) (list y y2)))               ; y = y2
                     (define yw (lem k3 `(BinW ,m) (list y)))
                     (cond
                       [(not t)
                        (define a2 (have k3 (Ad y y x2) yy (leibF `(not ,(Ad LHOLE LHOLE x2)) y y2)))
                        (add-uq k3 y y x x2 yw a2)]
                       [else
                        (define a2 (have k3 (Ad y y t2) yy (leibF `(not ,(Ad LHOLE LHOLE t2)) y y2)))
                        (define tt (add-uq k3 y y t t2 yw a2))                   ; t = t2
                        (define s2 (have k3 `(pr Suc ,x2 ,t) tt (leibF `(not (pr Suc ,x2 ,LHOLE)) t t2)))
                        (suc-uq k3 x x2 t s2)]))))))]))))

(defbin BinPos (key)
  (define n (cadr key))
  (closed-lemma key 1 (lambda (x) (list (Bin n x))) (lambda (x) `(ex kk (pr Suc ,x kk)))
    (lambda (k x)
      (define goal `(ex kk (pr Suc ,x kk)))
      (cond [(= n 1) (ex-i k (have k `(pr Suc ,x 3)) 3 goal)]
            [else
             (define m (quotient n 2))
             (bin-open k n x (have k (Bin n x))
               (lambda (k2 y t)
                 (cond
                   [t (ex-i k2 (have k2 `(pr Suc ,x ,t)) t goal)]
                   [else
                    ;; y = S(j): y + y = y + S(j) = S(y + j)
                    (define yw (lem k2 `(BinW ,m) (list y)))
                    (ex-e k2 (lem k2 `(BinPos ,m) (list y))
                      (lambda (k3 j)
                        (define jw (have k3 `(in ,j 0) (U 'KAddW (list 0 1 2 3 3 3 3)) (ac '(pr Emp 3)) (zerow k3 3)
                                         (use (rp 84) '() 0 j y) (U (rp 24) '()) (unf k3 'Sub (list y 0) (have k3 `(pr Sub ,y 0) (use (rp 71) '() 0 y) yw))))
                        (ex-e k3 (add-ex k3 y j yw jw)
                          (lambda (k4 u)
                            (ex-e k4 (suc-ex k4 u)
                              (lambda (k5 s)
                                (define a1 (add-s k5 y j u y s jw))              ; Ad(y,y,s)
                                (define xs (add-uq k5 y y x s yw a1))
                                (have k5 goal xs (ex-i k5 (have k5 `(pr Suc ,s ,u)) u `(ex kk (pr Suc ,s kk)))
                                      (leibF `(not (ex kk (pr Suc ,LHOLE kk))) x s))))))))])))]))))
