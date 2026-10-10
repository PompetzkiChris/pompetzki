#lang racket/base
;; kernel4-v5.rkt -- kernel4-v4.rkt with D in w supplied to the last associativity step of KX4. v4: kernel4-v3.rkt with one surplus bracket removed in KCancel (v3 did not read).
;; bin-v6 (for its helpers). Not trusted; checked step by step by core-v1's copy of the checker, then by the judges.
;;   KMul0L   Ctx -> forall z (z in w -> Mu(o,z,o))                                         0 * z = 0
;;   KX4      Ctx -> forall x y u v A B C D E (x,y,u,v in w -> Ad(x,y,A) -> Ad(u,v,B) -> Ad(A,B,E) -> Ad(x,u,C) ->
;;                     Ad(y,v,D) -> Ad(C,D,E))                                               (x+y)+(u+v) = (x+u)+(y+v)
;;   KMulAs   Ctx -> forall z (z in w -> forall x y q r s (x,y in w -> Mu(y,z,q) -> Mu(x,q,r) -> Mu(x,y,s) -> Mu(s,z,r)))
;;                                                                                           x(yz) = (xy)z
;;   KRDist   Ctx -> forall z (z in w -> forall a b c p q r (a,b in w -> Ad(a,b,c) -> Mu(a,z,p) -> Mu(b,z,q) ->
;;                     Ad(p,q,r) -> Mu(c,z,r)))                                              (a+b)z = az + bz
;;   KCancel  Ctx -> forall z (z in w -> forall x y v (x,y in w -> Ad(x,z,v) -> Ad(y,z,v) -> x = y))
;;   KZeroSum Ctx -> forall a b (a,b in w -> Ad(a,b,o) -> Emp(a))
;;   KMulNZ   Ctx -> forall e e1 x E (e1 in w -> x in w -> Suc(e,e1) -> not Emp(x) -> Mu(e,x,E) -> not Emp(E))
(require racket/list racket/match (file "C:/ClaudeOutput/pompetzki/lanes/L2D/core-v1.rkt")
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/nd-v3.rkt")
         (except-in (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel-v6.rkt") ids)
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel2-v2.rkt")
         (file "C:/ClaudeOutput/pompetzki/lanes/L2D/kernel3-v4.rkt")
         (only-in (file "C:/ClaudeOutput/pompetzki/lanes/L2D/bin-v6.rkt") closed-lemma lem last-consequent dist-inst
                  pred-in trans-w rw-fwd rw-bwd))
(provide (all-defined-out))

(define (ind-lemma key phi base step)          ; Ctx -> forall z (z in w -> phi(z)) by induction
  (begin-thm! key 4)
  (define k (kctx))
  (induct k phi base step)
  (define zz (gs 'z))
  (end-thm! (ac `(imp ,CTX-DSL (all ,zz (imp (in ,zz 0) ,(phi zz))))) (ids 4)))
;; use an induction lemma: forall z (z in w -> forall ... (h -> ... -> c)) at z and the rest
(define (ind-use k key z rest . ls)
  (define f (all-e k (lemma-fact k key) z))
  (define g (have k (rhs-of (concl k f)) f ls))
  (define inst (apply all-e k g rest))
  (have k (last-consequent (concl k inst)) inst ls))

;; ------------------------------------------------------------------ 0 * z = 0
(defkey KMul0L (key)
  (ind-lemma key (lambda (v) (Mu 3 v 3))
    (lambda (k) (mul-z k 3 (zerow k 3)))
    (lambda (k d t lphi) (mul-s k 3 d 3 t 3 lphi (add-z k 3 (zerow k 3))))))
(define (mul0l k z . ls) (ind-use k 'KMul0L z '() ls))

;; ------------------------------------------------------------------ the interchange of four
(defkey KX4 (key)
  (closed-lemma key 9
    (lambda (x y u v A B C D E) (list `(in ,x 0) `(in ,y 0) `(in ,u 0) `(in ,v 0) (Ad x y A) (Ad u v B) (Ad A B E) (Ad x u C) (Ad y v D)))
    (lambda (x y u v A B C D E) (Ad C D E))
    (lambda (k x y u v A B C D E)
      ;; (x+y)+B = E  =>  x + (y+B) = E;  y + B = y + (u+v) = (y+u)+v = (u+y)+v = u + (y+v) = u + D
      ;; so x + (u + D) = E, and (x+u)+D = x+(u+D)  =>  C + D = E
      (define Bw (add-w k u v B)) (define Dw (add-w k y v D)) (define Cw (add-w k x u C))
      (ex-e k (add-ex k y B Bw)
        (lambda (k2 yB)
          (define e1 (add-assoc k2 x y B A E yB Bw))                ; Ad(x,yB,E)
          (ex-e k2 (add-ex k2 y u)
            (lambda (k3 yu)
              (define yuw (add-w k3 y u yu))
              (ex-e k3 (add-ex k3 yu v yuw)
                (lambda (k4 r)
                  (define e2 (add-assoc k4 y u v yu r B))           ; (y+u)+v = r, u+v = B => y + B = r
                  (define e3 (add-uq k4 y B yB r Bw e2))             ; yB = r
                  (define uy (add-comm k4 y u yu))                  ; Ad(u,y,yu)
                  (define e4 (add-assoc k4 u y v yu r D uy))         ; (u+y)+v = r, y+v = D => u + D = r
                  (ex-e k4 (add-ex k4 C D Cw Dw)
                    (lambda (k5 F)
                      (define e5 (add-assoc k5 x u D C F r e4 Dw))      ; (x+u)+D = F, u+D = r => x + r = F
                      (define rw (add-w k5 u D r e4))
                      (define e6 (rw-fwd k5 (lambda (h) (Ad x h E)) yB r e3 e1))   ; Ad(x,r,E)
                      (define e7 (add-uq k5 x r E F rw e6 e5))       ; E = F
                      (define CF (have k5 (Ad C D F)))
                      (rw-bwd k5 (lambda (h) (Ad C D h)) E F e7 CF))))))))))))

;; ------------------------------------------------------------------ x(yz) = (xy)z
(define (mulas-phi zz)
  (define-values (x y q r s) (values (gs 'x) (gs 'y) (gs 'q) (gs 'r) (gs 's)))
  `(all ,x ,y ,q ,r ,s (imp (in ,x 0) (in ,y 0) ,(Mu y zz q) ,(Mu x q r) ,(Mu x y s) ,(Mu s zz r))))
(defkey KMulAs (key)
  (define (hy zz) (lambda (x y q r s) (list `(in ,x 0) `(in ,y 0) (Mu y zz q) (Mu x q r) (Mu x y s))))
  (define (cn zz) (lambda (x y q r s) (Mu s zz r)))
  (ind-lemma key mulas-phi
    (lambda (k)
      (close-all k 5 (hy 3) (cn 3)
        (lambda (k2 x y q r s)
          (define ow (zerow k2 3))
          (define qo (mul-uq k2 y 3 q 3 ow (mul-z k2 y)))
          (define m1 (rw-fwd k2 (lambda (h) (Mu x h r)) q 3 qo))
          (define ro (mul-uq k2 x 3 r 3 ow m1 (mul-z k2 x)))
          (define sw (mul-w k2 x y s))
          (rw-bwd k2 (lambda (h) (Mu s 3 h)) r 3 ro (mul-z k2 s sw)))
        (mulas-phi 3)))
    (lambda (k d t lphi)
      (close-all k 5 (hy t) (cn t)
        (lambda (k2 x y q r s)
          (define tw (sucw k2 d t))
          (define sw (mul-w k2 x y s))
          (ex-e k2 (mul-ex k2 y d)
            (lambda (k3 q0)
              (define q0w (mul-w k3 y d q0))
              (ex-e k3 (add-ex k3 y q0 q0w)
                (lambda (k4 q1)
                  (define qq (mul-uq k4 y t q q1 tw (mul-s k4 y d q0 t q1)))    ; q = q1 = y + q0
                  (ex-e k4 (mul-ex k4 x q0 q0w)
                    (lambda (k5 r0)
                      (define r0w (mul-w k5 x q0 r0))
                      (ex-e k5 (add-ex k5 s r0 sw r0w)
                        (lambda (k6 R)
                          (define q1w (add-w k6 y q0 q1))
                          (define m1 (dist-inst k6 q0 x y q1 s r0 R q0w))        ; x(y + q0) = xy + x q0 = R
                          (define m2 (rw-fwd k6 (lambda (h) (Mu x h r)) q q1 qq))
                          (define rR (mul-uq k6 x q1 r R q1w m2 m1))              ; r = R
                          (define ih (have k6 (Mu s d r0) (all-e k6 lphi x y q0 r0 s)))
                          (define m3 (mul-s k6 s d r0 t R ih))                    ; Mu(s,t,R)
                          (rw-bwd k6 (lambda (h) (Mu s t h)) r R rR m3))))))))))
        (mulas-phi t)))))

;; ------------------------------------------------------------------ (a+b)z = az + bz
(define (rdist-phi zz)
  (define-values (a b c p q r) (values (gs 'a) (gs 'b) (gs 'c) (gs 'p) (gs 'q) (gs 'r)))
  `(all ,a ,b ,c ,p ,q ,r (imp (in ,a 0) (in ,b 0) ,(Ad a b c) ,(Mu a zz p) ,(Mu b zz q) ,(Ad p q r) ,(Mu c zz r))))
(defkey KRDist (key)
  (define (hy zz) (lambda (a b c p q r) (list `(in ,a 0) `(in ,b 0) (Ad a b c) (Mu a zz p) (Mu b zz q) (Ad p q r))))
  (define (cn zz) (lambda (a b c p q r) (Mu c zz r)))
  (ind-lemma key rdist-phi
    (lambda (k)
      (close-all k 6 (hy 3) (cn 3)
        (lambda (k2 a b c p q r)
          (define ow (zerow k2 3))
          (define po (mul-uq k2 a 3 p 3 ow (mul-z k2 a)))
          (define qo (mul-uq k2 b 3 q 3 ow (mul-z k2 b)))
          (define a1 (rw-fwd k2 (lambda (h) (Ad h q r)) p 3 po))
          (define a2 (rw-fwd k2 (lambda (h) (Ad 3 h r)) q 3 qo a1))
          (define ro (add-uq k2 3 3 r 3 ow a2 (add-z k2 3 ow)))
          (define cw (add-w k2 a b c))
          (rw-bwd k2 (lambda (h) (Mu c 3 h)) r 3 ro (mul-z k2 c cw)))
        (rdist-phi 3)))
    (lambda (k d t lphi)
      (close-all k 6 (hy t) (cn t)
        (lambda (k2 a b c p q r)
          (define tw (sucw k2 d t))
          (define cw (add-w k2 a b c))
          (ex-e k2 (mul-ex k2 a d)
            (lambda (k3 p0)
              (define p0w (mul-w k3 a d p0))
              (ex-e k3 (add-ex k3 a p0 p0w)
                (lambda (k4 p1)
                  (define pp (mul-uq k4 a t p p1 tw (mul-s k4 a d p0 t p1)))     ; p = a + p0
                  (ex-e k4 (mul-ex k4 b d)
                    (lambda (k5 q0)
                      (define q0w (mul-w k5 b d q0))
                      (ex-e k5 (add-ex k5 b q0 q0w)
                        (lambda (k6 q1)
                          (define qq (mul-uq k6 b t q q1 tw (mul-s k6 b d q0 t q1)))   ; q = b + q0
                          (ex-e k6 (add-ex k6 p0 q0 p0w q0w)
                            (lambda (k7 r0)
                              (define ih (have k7 (Mu c d r0) (all-e k7 lphi a b c p0 q0 r0)))
                              (define r0w (add-w k7 p0 q0 r0))
                              ;; r = p + q = (a + p0) + (b + q0) = (a + b) + (p0 + q0) = c + r0
                              (define a1 (rw-fwd k7 (lambda (h) (Ad h q r)) p p1 pp))
                              (define a2 (rw-fwd k7 (lambda (h) (Ad p1 h r)) q q1 qq a1))
                              (define x4 (lem k7 (quote KX4) (list a p0 b q0 p1 q1 c r0 r) p0w q0w a2))
                              (define m1 (mul-s k7 c d r0 t r ih x4))
                              m1)))))))))))
        (rdist-phi t)))))

;; ------------------------------------------------------------------ Suc injective: Suc(s,a) & Suc(s,b) -> a = b
(defkey KSucInj (key)
  (closed-lemma key 3 (lambda (a b s) (list `(pr Suc ,s ,a) `(pr Suc ,s ,b))) (lambda (a b s) `(eq ,a ,b))
    (lambda (k a b s)
      (define as (pred-in k s a))
      (define bs (pred-in k s b))
      (define db (have k (def-rhs (defn 'Suc (list s b))) (defn 'Suc (list s b))))
      (define da (have k (def-rhs (defn 'Suc (list s a))) (defn 'Suc (list s a))))
      (define i1 (all-e k db a))                                  ; a in s <-> a in b or a = b
      (define i2 (all-e k da b))                                  ; b in s <-> b in a or b = a
      (define nt (use (rp 26) '() a b))                           ; not (a in b & b in a)
      (define sym (have k `(imp (eq ,b ,a) (eq ,a ,b)) (leibF `(eq ,LHOLE ,b) b a) (Y (Eqv b b))))
      (have k `(eq ,a ,b) as bs i1 i2 nt sym))))
(define (suc-inj k a b s . ls) (lem k 'KSucInj (list a b s) ls))

;; ------------------------------------------------------------------ cancellation: x + z = v, y + z = v -> x = y
(define (cancel-phi zz)
  (define-values (x y v) (values (gs 'x) (gs 'y) (gs 'v)))
  `(all ,x ,y ,v (imp (in ,x 0) (in ,y 0) ,(Ad x zz v) ,(Ad y zz v) (eq ,x ,y))))
(defkey KCancel (key)
  (define (hy zz) (lambda (x y v) (list `(in ,x 0) `(in ,y 0) (Ad x zz v) (Ad y zz v))))
  (define (cn x y v) `(eq ,x ,y))
  (ind-lemma key cancel-phi
    (lambda (k)
      (close-all k 3 (hy 3) cn
        (lambda (k2 x y v)
          (define ow (zerow k2 3))
          (define vx (add-uq k2 x 3 v x ow (add-z k2 x)))
          (define vy (add-uq k2 y 3 v y ow (add-z k2 y)))
          (rw-fwd k2 (lambda (h) `(eq ,h ,y)) v x vx vy))
        (cancel-phi 3)))
    (lambda (k d t lphi)
      (close-all k 3 (hy t) cn
        (lambda (k2 x y v)
          (define tw (sucw k2 d t))
          (ex-e k2 (add-ex k2 x d)
            (lambda (k3 v0)
              (ex-e k3 (suc-ex k3 v0)
                (lambda (k4 v1)
                  (define e1 (add-uq k4 x t v v1 tw (add-s k4 x d v0 t v1)))      ; v = v1
                  (ex-e k4 (add-ex k4 y d)
                    (lambda (k5 u0)
                      (ex-e k5 (suc-ex k5 u0)
                        (lambda (k6 u1)
                          (define e2 (add-uq k6 y t v u1 tw (add-s k6 y d u0 t u1)))  ; v = u1
                          ;; Suc(v,v0) and Suc(v,u0)
                          (define s1 (rw-bwd k6 (lambda (h) `(pr Suc ,h ,v0)) v v1 e1))
                          (define s2 (rw-bwd k6 (lambda (h) `(pr Suc ,h ,u0)) v u1 e2))
                          (define e3 (suc-inj k6 v0 u0 v s1 s2))                       ; v0 = u0
                          (define a1 (rw-bwd k6 (lambda (h) (Ad y d h)) v0 u0 e3))     ; Ad(y,d,v0)
                          (have k6 `(eq ,x ,y) (all-e k6 lphi x y v0) a1))))))))))
        (cancel-phi t)))))
(define (cancel k z x y v . ls) (ind-use k 'KCancel z (list x y v) ls))

;; ------------------------------------------------------------------ a + b = 0 -> a = 0
(defkey KZeroSum (key)
  (closed-lemma key 2 (lambda (a b) (list `(in ,a 0) `(in ,b 0) (Ad a b 3))) (lambda (a b) `(pr Emp ,a))
    (lambda (k a b)
      (define cs (have k `(or (pr Emp ,b) (ex yy (and (in yy 0) (pr Suc ,b yy)))) (use (rp 111) '() 0 b)))
      ;; Emp(b): b = o, a + o = o, a + o = a, so a = o
      (define kE (cx+ k `(pr Emp ,b)))
      (define bo (emp-uq kE b 3))
      (define a1 (rw-fwd kE (lambda (h) (Ad a h 3)) b 3 bo))
      (define ao (add-uq kE a 3 3 a (zerow kE 3) a1 (add-z kE a)))
      (define eE (rw-fwd kE (lambda (h) `(pr Emp ,h)) 3 a ao))
      (define c1 (discharge k `(pr Emp ,b) eE))
      ;; Suc(b,y): a + b = S(a + y), not empty, contradiction
      (define X `(ex yy (and (in yy 0) (pr Suc ,b yy))))
      (define kS (cx+ k X))
      (define r2
        (ex-e kS (have kS X)
          (lambda (k3 y)
            (ex-e k3 (add-ex k3 a y)
              (lambda (k4 q)
                (ex-e k4 (suc-ex k4 q)
                  (lambda (k5 s)
                    (define a2 (add-s k5 a y q b s))                       ; Ad(a,b,s)
                    (define os (add-uq k5 a b 3 s a2))                     ; o = s
                    (define qs (pred-in k5 s q))
                    (define q3 (rw-bwd k5 (lambda (h) `(in ,q ,h)) 3 s os qs))   ; q in o
                    (define d (defn 'Emp (list 3)))
                    (define nq (all-e k5 (have k5 (def-rhs d) d) q))      ; not q in o
                    (have k5 `(pr Emp ,a) q3 nq))))))))
      (define c2 (discharge k X r2))
      (have k `(pr Emp ,a) cs c1 c2))))
(define (zero-sum k a b . ls) (lem k 'KZeroSum (list a b) ls))

;; ------------------------------------------------------------------ e >= 1, x /= 0, e*x = E -> E /= 0
(defkey KMulNZ (key)
  (closed-lemma key 4 (lambda (e e1 x E) (list `(in ,e1 0) `(in ,x 0) `(pr Suc ,e ,e1) `(not (pr Emp ,x)) (Mu e x E)))
    (lambda (e e1 x E) `(not (pr Emp ,E)))
    (lambda (k e e1 x E)
      (define cs (have k `(or (pr Emp ,x) (ex yy (and (in yy 0) (pr Suc ,x yy)))) (use (rp 111) '() 0 x)))
      (define c1 (have k `(imp (pr Emp ,x) (not (pr Emp ,E)))))          ; contradicts not Emp(x)
      (define X `(ex yy (and (in yy 0) (pr Suc ,x yy))))
      (define kS (cx+ k X))
      (define r2
        (ex-e kS (have kS X)
          (lambda (k3 x1)
            (define ew (sucw k3 e1 e))
            (ex-e k3 (mul-ex k3 e x1 ew)
              (lambda (k4 m)
                (define mw (mul-w k4 e x1 m))
                (ex-e k4 (add-ex k4 e m ew mw)
                  (lambda (k5 E2)
                    (define m1 (mul-s k5 e x1 m x E2))                    ; Mu(e,x,E2)
                    (define ee (mul-uq k5 e x E E2 m1))                   ; E = E2
                    ;; Emp(E) -> contradiction
                    (define k6 (cx+ k5 `(pr Emp ,E)))
                    (define eo (emp-uq k6 E 3))
                    (define a1 (rw-bwd k6 (lambda (h) (Ad e m h)) E E2 ee))     ; Ad(e,m,E)
                    (define a2 (rw-fwd k6 (lambda (h) (Ad e m h)) E 3 eo a1))   ; Ad(e,m,o)
                    (define ze (zero-sum k6 e m ew mw a2))                       ; Emp(e)
                    (define ie (pred-in k6 e e1))
                    (define d (defn 'Emp (list e)))
                    (define ni (all-e k6 (have k6 (def-rhs d) d ze) e1))
                    (define bad (have k6 `(not (pr Emp ,E)) ie ni))
                    (have k5 `(not (pr Emp ,E)) (discharge k5 `(pr Emp ,E) bad)))))))))
      (define c2 (discharge k X r2))
      (have k `(not (pr Emp ,E)) cs c1 c2))))
