#lang racket/base
;; kernel4-v1.rkt -- lane L2D: further laws on omega for the Farkas emitter, over kernel-v6, kernel2-v2, kernel3-v4 and
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
                      (define e5 (add-assoc k5 x u D C F r e4))      ; (x+u)+D = F, u+D = r => x + r = F
                      (define rw (add-w k5 u D r))
                      (define e6 (rw-fwd k5 (lambda (h) (Ad x h E)) yB r e3 e1))   ; Ad(x,r,E)
                      (define e7 (add-uq k5 x r E F rw e6 e5))       ; E = F
                      (define CF (have k5 (Ad C D F) e5 (U 'KAddW (list 0 1 2 3 x u C))))
                      (rw-bwd k5 (lambda (h) (Ad C D h)) E F e7 CF))))))))))))))

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
                              (define x4 (have k7 (Ad c r0 r) (U 'KX4 (list 0 1 2 3)) ))
                              (define m1 (mul-s k7 c d r0 t r ih))
                              m1)))))))))))
        (rdist-phi t)))))
