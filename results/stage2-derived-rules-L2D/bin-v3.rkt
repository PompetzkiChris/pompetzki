#lang racket/base
;; bin-v3.rkt -- bin-v2.rkt with the closing brackets of BinUq, BinPos, BinAdd and BinMul corrected (v2 did not read).
;; lane L2D: binary numerals over the arithmetic kernel (kernel-v6, kernel2-v2, kernel3-v4).
;; v1 had a wrong instantiation helper and a wrong membership step in BinPos; v2 replaces them and adds BinInc,
;; BinAdd, BinMul, CMul, CAdd, CNZ. Not trusted; every lemma is checked by core-v1's copy of the checker as it is
;; built, then by the judges.
;;
;; Encoding of natural numbers (frame variables 0..3 = w, p, g, o under Ctx, as in the kernel):
;;   Bin_0(x) := Emp(x)          Bin_1(x) := Suc(x,o)
;;   Bin_2m(x)   := exists y (Bin_m(y) & Ad(y,y,x))                              m >= 1
;;   Bin_2m+1(x) := exists y (Bin_m(y) & exists t (Ad(y,y,t) & Suc(x,t)))       m >= 1
;; One existential per bit, about 5 nesting levels per bit (the pmp judge allows about 240 in all).
;; Lemmas, generated per number and cached by key (statements Ctx -> forall ...):
;;   (BinW n) Bin_n(x) -> x in w                (BinEx n) exists x Bin_n(x)       (BinUq n) Bin_n(x), Bin_n(x') -> x = x'
;;   (BinPos n) n >= 1: Bin_n(x) -> exists k Suc(x,k)        (BinInc n) Bin_n(x), Suc(s,x) -> Bin_n+1(s)
;;   (BinAdd a b) Bin_a(x), Bin_b(y), Ad(x,y,z) -> Bin_a+b(z)
;;   (BinMul a b) a >= 1: Bin_a(x), Bin_b(y), Mu(x,y,z) -> Bin_ab(z)
;;   (CAdd a b) Bin_a(x), Bin_b(y), Bin_a+b(z) -> Ad(x,y,z)       (CMul a b) a >= 1: Bin_a(x), Bin_b(y), Bin_ab(z) -> Mu(x,y,z)
;;   (CNZ n) n >= 1: Bin_n(x) -> not Emp(x)
;; General: KLA (interchange) Ctx -> forall a b A B s S (a,b in w -> Ad(a,a,A) -> Ad(b,b,B) -> Ad(a,b,s) -> Ad(s,s,S)
;;   -> Ad(A,B,S)).
;; Derivation length: BinAdd(a,b) O(bits) lemmas, BinMul(a,b) O(bits(b)) BinMul + O(bits^2) BinAdd lemmas.
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

;; a lemma  Ctx -> forall v1..vk (h1 -> ... -> c), proved in kctx with fresh variables (k = 0: Ctx -> c)
(define (closed-lemma key nv hyps con body)
  (begin-thm! key 4)
  (define k (kctx))
  (cond
    [(= nv 0) (body k) (end-thm! (ac `(imp ,CTX-DSL ,(con))) (ids 4))]
    [else
     (define names (for/list ([i nv]) (gs 'v)))
     (define goal `(all ,@names (imp ,@(apply hyps names) ,(apply con names))))
     (close-all k nv hyps con body goal)
     (end-thm! (ac `(imp ,CTX-DSL ,goal)) (ids 4))]))
(define (last-consequent f) (match f [(list 'I _ b) (last-consequent b)] [_ f]))
;; the instance of a closed lemma at frame variables vs, its consequent as a fact in k (hypotheses from k and ls)
(define (lem k key vs . ls)
  (define f (lemma-fact k key))
  (if (null? vs) f
      (let ([inst (apply all-e k f vs)]) (have k (last-consequent (concl k inst)) inst ls))))
;; KL1 instance: yy in w, xx in w, Ad(xx,yy,zz), Suc(xx1,xx), Suc(zz1,zz) -> Ad(xx1,yy,zz1)
(define (l1-inst k yy xx zz xx1 zz1 . ls)
  (define f (all-e k (lemma-fact k 'KL1) yy))
  (define g (have k (rhs-of (concl k f)) f ls))
  (have k (Ad xx1 yy zz1) (all-e k g xx zz xx1 zz1) ls))
;; KDist instance: zz,x,y in w, Ad(y,zz,s), Mu(x,y,p), Mu(x,zz,q), Ad(p,q,r) -> Mu(x,s,r)
(define (dist-inst k zz x y s p q r . ls)
  (define f (all-e k (lemma-fact k 'KDist) zz))
  (define g (have k (rhs-of (concl k f)) f ls))
  (have k (Mu x s r) (all-e k g x y s p q r) ls))
;; y in s from Suc(s,y)
(define (pred-in k s y . ls)
  (define d (defn 'Suc (list s y)))
  (define body (have k (def-rhs d) d ls))
  (have k `(in ,y ,s) (all-e k body y) (Y (Eqv y y))))
;; j in w from y in w and j in y (omega is transitive, replay 71)
(define (trans-w k j y . ls)
  (define sub (have k `(pr Sub ,y 0) (use (rp 71) '() 0 y) ls))
  (have k `(in ,j 0) (all-e k (unf k 'Sub (list y 0) sub) j) ls))

;; unfold Bin_n(x) (fact l), n >= 2: body gets (k2 y t), t = #f for even n (then Ad(y,y,x)), else Ad(y,y,t), Suc(x,t)
(define (bin-open k n x l body)
  (ex-e k l
    (lambda (k2 y)
      (if (even? n)
          (body k2 y #f)
          (ex-e k2 (have k2 `(ex tt (and ,(Ad y y 'tt) (pr Suc ,x tt))))
                (lambda (k3 t) (body k3 y t)))))))
;; Bin_n(x) from Bin_m(y) and Ad(y,y,x) (even), or Ad(y,y,t) and Suc(x,t) (odd)
(define (bin-pack k n x y t . ls)
  (define m (quotient n 2))
  (cond
    [(even? n) (ex-i k (have k `(and ,(Bin m y) ,(Ad y y x)) ls) y (Bin n x))]
    [else
     (define inner (ex-i k (have k `(and ,(Ad y y t) (pr Suc ,x ,t)) ls) t `(ex tt (and ,(Ad y y 'tt) (pr Suc ,x tt)))))
     (ex-i k (have k `(and ,(Bin m y) (ex tt (and ,(Ad y y 'tt) (pr Suc ,x tt)))) inner ls) y (Bin n x))]))
;; F[b] from F[a] and a = b  /  F[a] from F[b] and a = b   (F: variable -> formula)
(define (rw-fwd k F a b eqline . ls) (have k (F b) eqline ls (leibF (F LHOLE) a b)))
(define (rw-bwd k F a b eqline . ls) (have k (F a) eqline ls (leibF `(not ,(F LHOLE)) a b)))

(define-syntax-rule (defbin name (key) body ...) (hash-set! generators 'name (lambda (key) body ...)))

;; ------------------------------------------------------------------ KLA, the interchange law
(defkey KLA (key)
  (closed-lemma key 6
    (lambda (a b A B s S) (list `(in ,a 0) `(in ,b 0) (Ad a a A) (Ad b b B) (Ad a b s) (Ad s s S)))
    (lambda (a b A B s S) (Ad A B S))
    (lambda (k a b A B s S)
      (define Aw (add-w k a a A)) (define Bw (add-w k b b B)) (define sw (add-w k a b s))
      (ex-e k (add-ex k a B Bw)
        (lambda (k2 q)
          (ex-e k2 (add-ex k2 A B Aw Bw)
            (lambda (k3 v)
              (define aqv (add-assoc k3 a a B A v q Bw))                ; (a+a)+B = v, a+B = q  =>  a+q = v
              (ex-e k3 (add-ex k3 s b sw)
                (lambda (k4 r)
                  (define aBr (add-assoc k4 a b b s r B))               ; (a+b)+b = r, b+b = B  =>  a+B = r
                  (define qr (add-uq k4 a B q r Bw aBr))                 ; q = r
                  (ex-e k4 (add-ex k4 b s sw)
                    (lambda (k5 bs)
                      (define aBS (add-assoc k5 a b s s S bs sw))        ; (a+b)+s = S, b+s = bs  =>  a+bs = S
                      (define sbbs (add-comm k5 b s bs sw))              ; s+b = bs
                      (define rbs (add-uq k5 s b r bs sw sbbs))          ; r = bs
                      (define a1 (rw-fwd k5 (lambda (h) (Ad a h v)) q r qr aqv))
                      (define a2 (rw-fwd k5 (lambda (h) (Ad a h v)) r bs rbs a1))
                      (define bsw (add-w k5 b s bs))
                      (define vS (add-uq k5 a bs v S bsw a2 aBS))
                      (rw-fwd k5 (lambda (h) (Ad A B h)) v S vS))))))))))))

;; ------------------------------------------------------------------ BinW, BinEx, BinUq, BinPos
(defbin BinW (key)
  (define n (cadr key))
  (closed-lemma key 1 (lambda (x) (list (Bin n x))) (lambda (x) `(in ,x 0))
    (lambda (k x)
      (cond [(= n 0) (zerow k x)]
            [(= n 1) (sucw k 3 x (zerow k 3))]
            [else
             (bin-open k n x (have k (Bin n x))
               (lambda (k2 y t) (if t (sucw k2 t x (add-w k2 y y t)) (add-w k2 y y x))))]))))

(defbin BinEx (key)
  (define n (cadr key))
  (define (goal) `(ex xx ,(Bin n 'xx)))
  (closed-lemma key 0 #f goal
    (lambda (k)
      (cond [(= n 0) (ex-i k (have k `(pr Emp 3)) 3 (goal))]
            [(= n 1) (ex-e k (suc-ex k 3) (lambda (k2 s) (ex-i k2 (have k2 `(pr Suc ,s 3)) s (goal))))]
            [else
             (define m (quotient n 2))
             (ex-e k (lemma-fact k `(BinEx ,m))
               (lambda (k2 y)
                 (define yw (lem k2 `(BinW ,m) (list y)))
                 (ex-e k2 (add-ex k2 y y yw)
                   (lambda (k3 t)
                     (if (even? n)
                         (ex-i k3 (bin-pack k3 n t y #f) t (goal))
                         (ex-e k3 (suc-ex k3 t)
                           (lambda (k4 s) (ex-i k4 (bin-pack k4 n s y t) s (goal)))))))))]))))

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
                     (define yy (lem k3 `(BinUq ,m) (list y y2)))
                     (define yw (lem k3 `(BinW ,m) (list y)))
                     (cond
                       [(not t)
                        (define a2 (rw-bwd k3 (lambda (h) (Ad h h x2)) y y2 yy))
                        (add-uq k3 y y x x2 yw a2)]
                       [else
                        (define a2 (rw-bwd k3 (lambda (h) (Ad h h t2)) y y2 yy))
                        (define tt (add-uq k3 y y t t2 yw a2))
                        (define s2 (rw-bwd k3 (lambda (h) `(pr Suc ,x2 ,h)) t t2 tt))
                        (suc-uq k3 x x2 t s2)])))))]))))

(defbin BinPos (key)
  (define n (cadr key))
  (define (goal x) `(ex kk (pr Suc ,x kk)))
  (closed-lemma key 1 (lambda (x) (list (Bin n x))) goal
    (lambda (k x)
      (cond [(= n 1) (ex-i k (have k `(pr Suc ,x 3)) 3 (goal x))]
            [else
             (define m (quotient n 2))
             (bin-open k n x (have k (Bin n x))
               (lambda (k2 y t)
                 (cond
                   [t (ex-i k2 (have k2 `(pr Suc ,x ,t)) t (goal x))]
                   [else
                    (define yw (lem k2 `(BinW ,m) (list y)))
                    (ex-e k2 (lem k2 `(BinPos ,m) (list y))
                      (lambda (k3 j)
                        (define jy (pred-in k3 y j))
                        (define jw (trans-w k3 j y yw jy))
                        (ex-e k3 (add-ex k3 y j yw jw)
                          (lambda (k4 u)
                            (ex-e k4 (suc-ex k4 u)
                              (lambda (k5 s)
                                (define a1 (add-s k5 y j u y s jw))         ; Ad(y,y,s)
                                (define xs (add-uq k5 y y x s yw a1))       ; x = s
                                (define sx (rw-bwd k5 (lambda (h) `(pr Suc ,h ,u)) x s xs))
                                (ex-i k5 sx u (goal x)))))))])))]))))

;; ------------------------------------------------------------------ BinInc
(defbin BinInc (key)
  (define n (cadr key))
  (closed-lemma key 2 (lambda (x s) (list (Bin n x) `(pr Suc ,s ,x))) (lambda (x s) (Bin (add1 n) s))
    (lambda (k x s)
      (cond
        [(= n 0) (rw-fwd k (lambda (h) `(pr Suc ,s ,h)) x 3 (emp-uq k x 3))]
        [(= n 1)
         (define xw (sucw k 3 x (zerow k 3)))
         (define a1 (add-s k x 3 x x s (zerow k 3) (add-z k x xw)))     ; Ad(x,x,s)
         (bin-pack k 2 s x #f a1)]
        [else
         (define m (quotient n 2))
         (bin-open k n x (have k (Bin n x))
           (lambda (k2 y t)
             (cond
               [(not t) (bin-pack k2 (add1 n) s y x)]
               [else
                (define yw (lem k2 `(BinW ,m) (list y)))
                (ex-e k2 (suc-ex k2 y)
                  (lambda (k3 y1)
                    (define b1 (lem k3 `(BinInc ,m) (list y y1)))         ; Bin_m+1(y1)
                    (define y1w (sucw k3 y y1 yw))
                    (define a1 (add-s k3 y y t y1 x yw))                  ; Ad(y,y1,x)
                    (define a2 (l1-inst k3 y1 y x y1 s y1w yw a1))        ; Ad(y1,y1,s)
                    (bin-pack k3 (add1 n) s y1 #f b1 a2)))])))]))))

;; ------------------------------------------------------------------ BinAdd
(defbin BinAdd (key)
  (match-define (list _ a b) key)
  (closed-lemma key 3 (lambda (x y z) (list (Bin a x) (Bin b y) (Ad x y z))) (lambda (x y z) (Bin (+ a b) z))
    (lambda (k x y z)
      (define xw (lem k `(BinW ,a) (list x)))
      (define yw (lem k `(BinW ,b) (list y)))
      (cond
        [(= a 0)
         (define x3 (emp-uq k x 3))
         (define a1 (rw-fwd k (lambda (h) (Ad h y z)) x 3 x3))
         (define zy (add-uq k 3 y z y yw a1 (l0 k y yw)))
         (rw-bwd k (lambda (h) (Bin b h)) z y zy)]
        [(= b 0)
         (define y3 (emp-uq k y 3))
         (define a1 (rw-fwd k (lambda (h) (Ad x h z)) y 3 y3))
         (define zx (add-uq k x 3 z x (zerow k 3) a1 (add-z k x xw)))
         (rw-bwd k (lambda (h) (Bin a h)) z x zx)]
        [(= b 1)
         (ex-e k (suc-ex k x)
           (lambda (k2 s)
             (define a1 (add-s k2 x 3 x y s (zerow k2 3) (add-z k2 x xw)))   ; Ad(x,y,s)
             (define zs (add-uq k2 x y z s yw a1))
             (define bs (lem k2 `(BinInc ,a) (list x s)))
             (rw-bwd k2 (lambda (h) (Bin (+ a b) h)) z s zs bs)))]
        [(= a 1)
         (define a1 (add-comm k x y z xw yw))                                ; Ad(y,x,z)
         (lem k `(BinAdd ,b 1) (list y x z) a1)]
        [else
         (define a2 (quotient a 2)) (define b2 (quotient b 2)) (define c2 (+ a2 b2))
         (bin-open k a x (have k (Bin a x))
           (lambda (k2 x1 tx)
             (bin-open k2 b y (have k2 (Bin b y))
               (lambda (k3 y1 ty)
                 (define x1w (lem k3 `(BinW ,a2) (list x1)))
                 (define y1w (lem k3 `(BinW ,b2) (list y1)))
                 (define X (or tx x)) (define Yv (or ty y))
                 (define Xw (add-w k3 x1 x1 X)) (define Yw (add-w k3 y1 y1 Yv))
                 (ex-e k3 (add-ex k3 x1 y1 x1w y1w)
                   (lambda (k4 s1)
                     (define bs1 (lem k4 `(BinAdd ,a2 ,b2) (list x1 y1 s1)))       ; Bin_c2(s1)
                     (define s1w (add-w k4 x1 y1 s1))
                     (ex-e k4 (add-ex k4 s1 s1 s1w)
                       (lambda (k5 S2)
                         (define la (lem k5 'KLA (list x1 y1 X Yv s1 S2)))         ; Ad(X,Y,S2)
                         (define S2w (add-w k5 s1 s1 S2))
                         (cond
                           [(and (not tx) (not ty))
                            (define zS (add-uq k5 x y z S2 yw la))
                            (rw-bwd k5 (lambda (h) (Bin (+ a b) h)) z S2 zS (bin-pack k5 (* 2 c2) S2 s1 #f bs1))]
                           [(and tx (not ty))
                            (ex-e k5 (suc-ex k5 S2)
                              (lambda (k6 z1)
                                (define a1 (l1-inst k6 y tx S2 x z1 yw Xw la))             ; Ad(x,y,z1)
                                (define zz (add-uq k6 x y z z1 yw a1))
                                (rw-bwd k6 (lambda (h) (Bin (+ a b) h)) z z1 zz (bin-pack k6 (add1 (* 2 c2)) z1 s1 S2 bs1))))]
                           [(and (not tx) ty)
                            (ex-e k5 (suc-ex k5 S2)
                              (lambda (k6 z1)
                                (define a1 (add-s k6 x ty S2 y z1 Yw la))                  ; Ad(x,y,z1)
                                (define zz (add-uq k6 x y z z1 yw a1))
                                (rw-bwd k6 (lambda (h) (Bin (+ a b) h)) z z1 zz (bin-pack k6 (add1 (* 2 c2)) z1 s1 S2 bs1))))]
                           [else
                            (ex-e k5 (suc-ex k5 S2)
                              (lambda (k6 z1)
                                (define a1 (l1-inst k6 ty tx S2 x z1 Yw Xw la))            ; Ad(x,ty,z1)
                                (ex-e k6 (suc-ex k6 z1)
                                  (lambda (k7 z2)
                                    (define z1w (sucw k7 S2 z1 S2w))
                                    (define a2 (add-s k7 x ty z1 y z2 Yw a1))              ; Ad(x,y,z2)
                                    (define zz (add-uq k7 x y z z2 yw a2))
                                    (ex-e k7 (suc-ex k7 s1)
                                      (lambda (k8 u)
                                        (define bu (lem k8 `(BinInc ,c2) (list s1 u)))     ; Bin_c2+1(u)
                                        (define uw (sucw k8 s1 u s1w))
                                        (define a3 (add-s k8 s1 s1 S2 u z1 s1w))           ; Ad(s1,u,z1)
                                        (define a4 (l1-inst k8 u s1 z1 u z2 uw s1w a3))    ; Ad(u,u,z2)
                                        (rw-bwd k8 (lambda (h) (Bin (+ a b) h)) z z2 zz (bin-pack k8 (* 2 (add1 c2)) z2 u #f bu a4))))))))])))))))))]))))

;; ------------------------------------------------------------------ BinMul (a >= 1)
(defbin BinMul (key)
  (match-define (list _ a b) key)
  (closed-lemma key 3 (lambda (x y z) (list (Bin a x) (Bin b y) (Mu x y z))) (lambda (x y z) (Bin (* a b) z))
    (lambda (k x y z)
      (define xw (lem k `(BinW ,a) (list x)))
      (define yw (lem k `(BinW ,b) (list y)))
      (cond
        [(= b 0)
         (define y3 (emp-uq k y 3))
         (define m1 (rw-fwd k (lambda (h) (Mu x h z)) y 3 y3))
         (define z3 (mul-uq k x 3 z 3 (zerow k 3) m1 (mul-z k x xw)))
         (rw-bwd k (lambda (h) `(pr Emp ,h)) z 3 z3)]
        [(= b 1)
         (define m1 (mul-s k x 3 3 y x (zerow k 3) (mul-z k x xw) (add-z k x xw)))   ; Mu(x,y,x)
         (define zx (mul-uq k x y z x yw m1))
         (rw-bwd k (lambda (h) (Bin a h)) z x zx)]
        [else
         (define b2 (quotient b 2))
         (bin-open k b y (have k (Bin b y))
           (lambda (k2 y1 ty)
             (define y1w (lem k2 `(BinW ,b2) (list y1)))
             (define Yv (or ty y))
             (define Yw (add-w k2 y1 y1 Yv))
             (ex-e k2 (mul-ex k2 x y1 xw y1w)
               (lambda (k3 p)
                 (define bp (lem k3 `(BinMul ,a ,b2) (list x y1 p)))              ; Bin_ab2(p)
                 (define pw (mul-w k3 x y1 p))
                 (ex-e k3 (add-ex k3 p p pw)
                   (lambda (k4 P)
                     (define bP (bin-pack k4 (* 2 a b2) P p #f bp))               ; Bin_2ab2(P)
                     (define dm (dist-inst k4 y1 x y1 Yv p p P y1w xw))           ; Mu(x,Y,P)
                     (cond
                       [(not ty)
                        (define zP (mul-uq k4 x y z P yw dm))
                        (rw-bwd k4 (lambda (h) (Bin (* a b) h)) z P zP bP)]
                       [else
                        (define Pw (add-w k4 p p P))
                        (ex-e k4 (add-ex k4 x P xw Pw)
                          (lambda (k5 q)
                            (define bq (lem k5 `(BinAdd ,a ,(* 2 a b2)) (list x P q) bP))   ; Bin_a+2ab2(q)
                            (define m2 (mul-s k5 x ty P y q Yw dm))                         ; Mu(x,y,q)
                            (define zq (mul-uq k5 x y z q yw m2))
                            (rw-bwd k5 (lambda (h) (Bin (* a b) h)) z q zq bq)))])))))))]))))

;; ------------------------------------------------------------------ the atomic checks
(defbin CMul (key)
  (match-define (list _ a b) key)
  (closed-lemma key 3 (lambda (x y z) (list (Bin a x) (Bin b y) (Bin (* a b) z))) (lambda (x y z) (Mu x y z))
    (lambda (k x y z)
      (define xw (lem k `(BinW ,a) (list x)))
      (define yw (lem k `(BinW ,b) (list y)))
      (ex-e k (mul-ex k x y xw yw)
        (lambda (k2 z2)
          (define b2 (lem k2 `(BinMul ,a ,b) (list x y z2)))
          (define zz (lem k2 `(BinUq ,(* a b)) (list z z2) b2))
          (rw-bwd k2 (lambda (h) (Mu x y h)) z z2 zz))))))

(defbin CAdd (key)
  (match-define (list _ a b) key)
  (closed-lemma key 3 (lambda (x y z) (list (Bin a x) (Bin b y) (Bin (+ a b) z))) (lambda (x y z) (Ad x y z))
    (lambda (k x y z)
      (define xw (lem k `(BinW ,a) (list x)))
      (define yw (lem k `(BinW ,b) (list y)))
      (ex-e k (add-ex k x y xw yw)
        (lambda (k2 z2)
          (define b2 (lem k2 `(BinAdd ,a ,b) (list x y z2)))
          (define zz (lem k2 `(BinUq ,(+ a b)) (list z z2) b2))
          (rw-bwd k2 (lambda (h) (Ad x y h)) z z2 zz))))))

(defbin CNZ (key)
  (define n (cadr key))
  (closed-lemma key 1 (lambda (x) (list (Bin n x))) (lambda (x) `(not (pr Emp ,x)))
    (lambda (k x)
      (ex-e k (lem k `(BinPos ,n) (list x))
        (lambda (k2 j)
          (define jx (pred-in k2 x j))
          (define d (defn 'Emp (list x)))
          (have k2 `(not (pr Emp ,x)) d jx (V j (Imp (def-rhs d) (ren (scons j sid) (match (def-rhs d) [(list 'A f) f]))))))))))

(module+ main
  (load-base!)
  (reset-batch!)
  (define keys (for/list ([a (current-command-line-arguments)]) (with-input-from-string a read)))
  (for ([kk keys]) (ensure! kk))
  (define text (batch-text))
  (define-values (rg ths) (read-jdg-text text))
  (printf "theorems ~a steps ~a bytes ~a; copy of the checker: ~a\n" (length ths) (for/sum ([t ths]) (length (caddr t))) (string-length text) (check-batch rg ths))
  (for ([kk keys]) (printf "~a: ~a\n" kk (let ([s (show (reg-stmt (reg-index kk)))]) (substring s 0 (min 300 (string-length s)))))))
