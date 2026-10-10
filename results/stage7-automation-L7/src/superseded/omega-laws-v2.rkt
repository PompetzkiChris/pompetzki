#lang racket/base
;; omega-laws-v2.rkt -- lane L7, item 4: the laws of Add and Mul for all x, y, z in omega, each proved once by induction
;; (L:IndLem through the Ind schema of omega-base), from the recursion lemmas of omega-kind.
;; (v2 = v1 with one closing parenthesis fewer at the end of the step of MulSL.)
(require "l7core-v1.rkt" "omega-base-v1.rkt" "omega-kind-v5.rkt" racket/list racket/match)
(provide (all-defined-out))

(define (Add x y z) (add-f x y z))
(define (Mul x y z) (mul-f x y z))

;; an induction under the context H: the line H -> forall n (Nat n -> phi n)
;; base-k: (e He) -> line He -> phi(e), He = H & Emp(e);  step-k: (n m Hm) -> line Hm -> phi(m), Hm = (H & (Nat n & phi n)) & Suc(m,n)
(define (ind-proof H key params phi-gen base-k step-k)
  (define phi (apply phi-gen params))
  (define bl (all-under H (c (ind-B phi)) 1
                        (lambda (vs Mx) (define e (car vs))
                          (define He (Kf H (c `(pr Emp ,e))))
                          (T (list (base-k e He)) (Imp H Mx)))))
  (define sl (all-under H (c (ind-S phi)) 1
                        (lambda (vs Mx) (define n (car vs))
                          (define-values (natn r) (imp-parts Mx))
                          (define-values (phin ALLM) (imp-parts r))
                          (define Hn (Kf H (Kf natn phin)))
                          (define l (all-under Hn ALLM 1
                                               (lambda (vs2 Mx2) (define m (car vs2))
                                                 (define-values (sucmn phim) (imp-parts Mx2))
                                                 (define Hm (Kf Hn sucmn))
                                                 (T (list (step-k n m Hm)) (Imp Hn Mx2)))))
                          (T (list l) (Imp H Mx)))))
  (T (list bl sl (U key params)) (Imp H (c (ind-C phi)))))
;; a law: (need key) with its induction lemma built first
(define (law! key n ind-key k phi-gen deps body)
  (need key
   (lambda ()
     (for ([d deps]) (d))
     (ind! ind-key k (apply phi-gen (range k)))
     (lemma! key n body))))
;; H -> phi(v) with phi(v) = forall^k M: the matrix proved under H & antecedent
(define (under-all H F k prove)
  (all-under H F k (lambda (vs Mx)
                     (define-values (A B) (imp-parts Mx))
                     (define HA (Kf H A))
                     (T (list (prove vs HA)) (Imp H Mx)))))

;; ======================================================================== addition
;; AddZL: Emp(o) & Nat(y) -> Add(o,y,y)                      o y = 0 1
(define (phi-addzl o) (lambda (n) (Add o n n)))
(define (addzl!)
  (law! 'AddZL 2 '(IndAddZL) 1 phi-addzl (list (lambda () (kind-all! 'add)))
    (lambda ()
      (define-values (o y) (values 0 1))
      (define H (c `(pr Emp ,o)))
      (define l (ind-proof H '(IndAddZL) (list o) phi-addzl
                  (lambda (e He) (T (list (lu '(Z add) o e) (rs "L:EmpUq" o e) (leib (Add o e HOLE) o e)) (Imp He (c (Add o e e)))))
                  (lambda (n m Hm) (T (list (lu '(S add) o n n m m) (lu 'NatZero o)) (Imp Hm (c (Add o m m)))))))
      (T (list (fa-e l y)) (c `(imp (and (pr Emp ,o) (pr Nat ,y)) ,(Add o y y)))))))

;; AddSL: Nat x & Nat y & Suc(x2,x) & Add(x,y,z) & Suc(z2,z) -> Add(x2,y,z2)          x y x2 z z2 = 0..4
(define ((phi-addsl x x2) n) (let ([z (fresh-sym 'z)] [z2 (fresh-sym 'z)]) `(all ,z (all ,z2 (imp (and ,(Add x n z) (pr Suc ,z2 ,z)) ,(Add x2 n z2))))))
(define (addsl!)
  (law! 'AddSL 5 '(IndAddSL) 2 phi-addsl (list (lambda () (kind-all! 'add)))
    (lambda ()
      (define-values (x y x2 z z2) (values 0 1 2 3 4))
      (define H (c `(and (pr Nat ,x) (pr Suc ,x2 ,x))))
      (define l (ind-proof H '(IndAddSL) (list x x2) phi-addsl
                  (lambda (e He)
                    (under-all He (c ((phi-addsl x x2) e)) 2
                      (lambda (vs HA) (match-define (list z z2) vs)
                        (T (list (lu '(Zinv add) x e z) (leib `(pr Suc ,z2 ,HOLE) z x) (rs "L:SucUq" z2 x2 x)
                                 (lu '(Z add) x2 e) (leib `(not ,(Add x2 e HOLE)) z2 x2))
                           (Imp HA (c (Add x2 e z2)))))))
                  (lambda (n m Hm)
                    (under-all Hm (c ((phi-addsl x x2) m)) 2
                      (lambda (vs HA) (match-define (list z z2) vs)
                        (define goal (c (Add x2 m z2)))
                        (obt HA (list (lu '(Sinv add) x n m z)) (c (let ([w (fresh-sym 'w)]) `(ex ,w (and (pr Nat ,w) ,(Add x n w) (pr Suc ,z ,w)))))
                          (lambda (w _ Hw)
                            (T (append (inst* (c ((phi-addsl x x2) n)) (list w z))
                                       (list (lu '(S add) x2 n z m z2) (ru "H:NatSuc" x x2)))
                               (Imp Hw goal)))))))))
      (define l2 (fa-e (fa-e (fa-e l y) z) z2))
      (T (list l2) (c `(imp (and (pr Nat ,x) (pr Nat ,y) (pr Suc ,x2 ,x) ,(Add x y z) (pr Suc ,z2 ,z)) ,(Add x2 y z2)))))))

;; AddComm: Nat x & Nat y & Add(x,y,z) -> Add(y,x,z)          x y z = 0..2
(define ((phi-addcomm x) n) (let ([z (fresh-sym 'z)]) `(all ,z (imp ,(Add x n z) ,(Add n x z)))))
(define (addcomm!)
  (law! 'AddComm 3 '(IndAddComm) 1 phi-addcomm (list addzl! addsl!)
    (lambda ()
      (define-values (x y z) (values 0 1 2))
      (define H (c `(pr Nat ,x)))
      (define l (ind-proof H '(IndAddComm) (list x) phi-addcomm
                  (lambda (e He)
                    (under-all He (c ((phi-addcomm x) e)) 1
                      (lambda (vs HA) (match-define (list z) vs)
                        (T (list (lu '(Zinv add) x e z) (lu 'AddZL e x) (leib `(not ,(Add e x HOLE)) z x))
                           (Imp HA (c (Add e x z)))))))
                  (lambda (n m Hm)
                    (under-all Hm (c ((phi-addcomm x) m)) 1
                      (lambda (vs HA) (match-define (list z) vs)
                        (define goal (c (Add m x z)))
                        (obt HA (list (lu '(Sinv add) x n m z)) (c (let ([w (fresh-sym 'w)]) `(ex ,w (and (pr Nat ,w) ,(Add x n w) (pr Suc ,z ,w)))))
                          (lambda (w _ Hw)
                            (T (list (inst (c ((phi-addcomm x) n)) w) (lu 'AddSL n x m w z)) (Imp Hw goal)))))))))
      (T (list (fa-e (fa-e l y) z)) (c `(imp (and (pr Nat ,x) (pr Nat ,y) ,(Add x y z)) ,(Add y x z)))))))

;; AddAssoc: Nat x & Nat y & Nat z & Add(x,y,u) & Add(u,z,v) & Add(y,z,w) -> Add(x,w,v)       x y z u v w = 0..5
(define ((phi-addassoc x y) n)
  (let ([u (fresh-sym 'u)] [v (fresh-sym 'v)] [w (fresh-sym 'w)])
    `(all ,u (all ,v (all ,w (imp (and ,(Add x y u) ,(Add u n v) ,(Add y n w)) ,(Add x w v)))))))
(define (addassoc!)
  (law! 'AddAssoc 6 '(IndAddAssoc) 2 phi-addassoc (list (lambda () (kind-all! 'add)))
    (lambda ()
      (define-values (x y z u v w) (values 0 1 2 3 4 5))
      (define H (c `(and (pr Nat ,x) (pr Nat ,y))))
      (define l (ind-proof H '(IndAddAssoc) (list x y) phi-addassoc
                  (lambda (e He)
                    (under-all He (c ((phi-addassoc x y) e)) 3
                      (lambda (vs HA) (match-define (list u v w) vs)
                        (T (list (lu '(NatOp add) x y u) (lu '(Zinv add) u e v) (lu '(Zinv add) y e w)
                                 (leib `(not ,(Add x HOLE v)) w y) (leib `(not ,(Add x y HOLE)) v u))
                           (Imp HA (c (Add x w v)))))))
                  (lambda (n m Hm)
                    (under-all Hm (c ((phi-addassoc x y) m)) 3
                      (lambda (vs HA) (match-define (list u v w) vs)
                        (define goal (c (Add x w v)))
                        (obt HA (list (lu '(NatOp add) x y u) (lu '(Sinv add) u n m v))
                             (c (let ([q (fresh-sym 'q)]) `(ex ,q (and (pr Nat ,q) ,(Add u n q) (pr Suc ,v ,q)))))
                          (lambda (v0 _1 H1)
                            (obt H1 (list (lu '(Sinv add) y n m w))
                                 (c (let ([q (fresh-sym 'q)]) `(ex ,q (and (pr Nat ,q) ,(Add y n q) (pr Suc ,w ,q)))))
                              (lambda (w0 _2 H2)
                                (T (append (inst* (c ((phi-addassoc x y) n)) (list u v0 w0))
                                           (list (lu '(S add) x w0 v0 w v)))
                                   (Imp H2 goal)))))))))))
      (T (list (fa-e (fa-e (fa-e (fa-e l z) u) v) w))
         (c `(imp (and (pr Nat ,x) (pr Nat ,y) (pr Nat ,z) ,(Add x y u) ,(Add u z v) ,(Add y z w)) ,(Add x w v)))))))

;; ======================================================================== multiplication
;; MulZL: Emp(o) & Nat(y) -> Mul(o,y,o)          o y = 0 1
(define (phi-mulzl o) (lambda (n) (Mul o n o)))
(define (mulzl!)
  (law! 'MulZL 2 '(IndMulZL) 1 phi-mulzl (list (lambda () (kind-all! 'add) (kind-all! 'mul)))
    (lambda ()
      (define-values (o y) (values 0 1))
      (define H (c `(pr Emp ,o)))
      (define l (ind-proof H '(IndMulZL) (list o) phi-mulzl
                  (lambda (e He) (T (list (lu '(Z mul) o e) (rs "L:EmpUq" o e) (leib `(not ,(Mul o e HOLE)) o e)) (Imp He (c (Mul o e o)))))
                  (lambda (n m Hm) (T (list (lu '(S mul) o n o m o) (lu '(Z add) o o) (lu 'NatZero o)) (Imp Hm (c (Mul o m o)))))))
      (T (list (fa-e l y)) (c `(imp (and (pr Emp ,o) (pr Nat ,y)) ,(Mul o y o)))))))

;; MulSL: Nat x & Nat y & Suc(x2,x) & Mul(x,y,z) & Add(z,y,v) -> Mul(x2,y,v)      x y x2 z v = 0..4
(define ((phi-mulsl x x2) n) (let ([z (fresh-sym 'z)] [v (fresh-sym 'v)]) `(all ,z (all ,v (imp (and ,(Mul x n z) ,(Add z n v)) ,(Mul x2 n v))))))
(define (mulsl!)
  (law! 'MulSL 5 '(IndMulSL) 2 phi-mulsl (list (lambda () (kind-all! 'add) (kind-all! 'mul)) addassoc! addcomm!)
    (lambda ()
      (define-values (x y x2 z v) (values 0 1 2 3 4))
      (define H (c `(and (pr Nat ,x) (pr Suc ,x2 ,x))))
      (define (exq P) (c (let ([q (fresh-sym 'q)]) `(ex ,q ,(P q)))))
      (define l (ind-proof H '(IndMulSL) (list x x2) phi-mulsl
                  (lambda (e He)
                    (under-all He (c ((phi-mulsl x x2) e)) 2
                      (lambda (vs HA) (match-define (list z v) vs)
                        (T (list (lu '(Zinv mul) x e z) (lu 'NatZero e) (leib `(not (pr Nat ,HOLE)) z e)
                                 (lu '(Zinv add) z e v) (lu '(Z mul) x2 e)
                                 (leib `(eq ,v ,HOLE) z e) (leib `(not ,(Mul x2 e HOLE)) v e))
                           (Imp HA (c (Mul x2 e v)))))))
                  (lambda (n m Hm)
                    (under-all Hm (c ((phi-mulsl x x2) m)) 2
                      (lambda (vs HA) (match-define (list z v) vs)
                        (define goal (c (Mul x2 m v)))
                        (obt HA (list (lu '(Sinv mul) x n m z)) (exq (lambda (q) `(and (pr Nat ,q) ,(Mul x n q) ,(Add q x z))))
                          (lambda (z0 _1 H1)
                            (obt H1 (list (lu '(Tot add) z0 n)) (exq (lambda (q) `(and (pr Nat ,q) ,(Add z0 n q))))
                              (lambda (v0 _2 H2)
                                (obt H2 (list (lu '(Tot add) x n)) (exq (lambda (q) `(and (pr Nat ,q) ,(Add x n q))))
                                  (lambda (t _3 H3)
                                    (obt H3 (list (lu '(NatOp add) z0 x z) (lu '(Tot add) z n)) (exq (lambda (q) `(and (pr Nat ,q) ,(Add z n q))))
                                      (lambda (b _4 H4)
                                        (obt H4 (list (lu '(Tot add) v0 x)) (exq (lambda (q) `(and (pr Nat ,q) ,(Add v0 x q))))
                                          (lambda (cc _5 H5)
                                            (obt H5 (list (ru "H:SucEx" b)) (exq (lambda (q) `(pr Suc ,q ,b)))
                                              (lambda (sb _6 H6)
                                                (T (append (inst* (c ((phi-mulsl x x2) n)) (list z0 v0))
                                                           (list (lu 'AddAssoc z0 x n z b t) (lu 'AddComm x n t) (lu 'AddAssoc z0 n x v0 cc t)
                                                                 (lu '(Uq add) z0 t b cc) (leib `(pr Suc ,sb ,HOLE) b cc)
                                                                 (lu '(S add) v0 x cc x2 sb) (lu '(S add) z n b m sb) (ru "H:NatSuc" n m)
                                                                 (lu '(Uq add) z m v sb) (leib `(not ,(Add v0 x2 HOLE)) v sb)
                                                                 (ru "H:NatSuc" x x2) (lu '(S mul) x2 n v0 m v) (lu '(NatOp add) z0 x z)))
                                                   (Imp H6 goal)))))))))))))))))))
      (define l2 (fa-e (fa-e (fa-e l y) z) v))
      (T (list l2) (c `(imp (and (pr Nat ,x) (pr Nat ,y) (pr Suc ,x2 ,x) ,(Mul x y z) ,(Add z y v)) ,(Mul x2 y v)))))))

;; MulComm: Nat x & Nat y & Mul(x,y,z) -> Mul(y,x,z)       x y z = 0..2
(define ((phi-mulcomm x) n) (let ([z (fresh-sym 'z)]) `(all ,z (imp ,(Mul x n z) ,(Mul n x z)))))
(define (mulcomm!)
  (law! 'MulComm 3 '(IndMulComm) 1 phi-mulcomm (list mulzl! mulsl!)
    (lambda ()
      (define-values (x y z) (values 0 1 2))
      (define H (c `(pr Nat ,x)))
      (define l (ind-proof H '(IndMulComm) (list x) phi-mulcomm
                  (lambda (e He)
                    (under-all He (c ((phi-mulcomm x) e)) 1
                      (lambda (vs HA) (match-define (list z) vs)
                        (T (list (lu '(Zinv mul) x e z) (lu 'MulZL e x) (leib `(not ,(Mul e x HOLE)) z e))
                           (Imp HA (c (Mul e x z)))))))
                  (lambda (n m Hm)
                    (under-all Hm (c ((phi-mulcomm x) m)) 1
                      (lambda (vs HA) (match-define (list z) vs)
                        (define goal (c (Mul m x z)))
                        (obt HA (list (lu '(Sinv mul) x n m z)) (c (let ([w (fresh-sym 'w)]) `(ex ,w (and (pr Nat ,w) ,(Mul x n w) ,(Add w x z)))))
                          (lambda (w _ Hw)
                            (T (list (inst (c ((phi-mulcomm x) n)) w) (lu 'MulSL n x m w z)) (Imp Hw goal)))))))))
      (T (list (fa-e (fa-e l y) z)) (c `(imp (and (pr Nat ,x) (pr Nat ,y) ,(Mul x y z)) ,(Mul y x z)))))))

;; DistL: Nat x & Nat y & Nat z & Add(y,z,s) & Mul(x,s,p) & Mul(x,y,a) & Mul(x,z,b) -> Add(a,b,p)     x y z s p a b = 0..6
(define ((phi-distl x y) n)
  (let ([s (fresh-sym 's)] [p (fresh-sym 'p)] [a (fresh-sym 'a)] [b (fresh-sym 'b)])
    `(all ,s (all ,p (all ,a (all ,b (imp (and ,(Add y n s) ,(Mul x s p) ,(Mul x y a) ,(Mul x n b)) ,(Add a b p))))))))
(define (distl!)
  (law! 'DistL 7 '(IndDistL) 2 phi-distl (list (lambda () (kind-all! 'add) (kind-all! 'mul)) addassoc!)
    (lambda ()
      (define-values (x y z s p a b) (values 0 1 2 3 4 5 6))
      (define H (c `(and (pr Nat ,x) (pr Nat ,y))))
      (define (exq P) (c (let ([q (fresh-sym 'q)]) `(ex ,q ,(P q)))))
      (define l (ind-proof H '(IndDistL) (list x y) phi-distl
                  (lambda (e He)
                    (under-all He (c ((phi-distl x y) e)) 4
                      (lambda (vs HA) (match-define (list s p a b) vs)
                        (T (list (lu '(Zinv add) y e s) (lu '(Zinv mul) x e b) (leib (Mul x HOLE p) s y) (lu '(Uq mul) x y p a)
                                 (lu '(Z add) a e) (leib `(not ,(Add a b HOLE)) p a) (leib `(not ,(Add a HOLE a)) b e))
                           (Imp HA (c (Add a b p)))))))
                  (lambda (n m Hm)
                    (under-all Hm (c ((phi-distl x y) m)) 4
                      (lambda (vs HA) (match-define (list s p a b) vs)
                        (define goal (c (Add a b p)))
                        (obt HA (list (lu '(Sinv add) y n m s)) (exq (lambda (q) `(and (pr Nat ,q) ,(Add y n q) (pr Suc ,s ,q))))
                          (lambda (s0 _1 H1)
                            (obt H1 (list (lu '(Sinv mul) x s0 s p)) (exq (lambda (q) `(and (pr Nat ,q) ,(Mul x s0 q) ,(Add q x p))))
                              (lambda (p0 _2 H2)
                                (obt H2 (list (lu '(Sinv mul) x n m b)) (exq (lambda (q) `(and (pr Nat ,q) ,(Mul x n q) ,(Add q x b))))
                                  (lambda (b0 _3 H3)
                                    (T (append (inst* (c ((phi-distl x y) n)) (list s0 p0 a b0))
                                               (list (lu 'AddAssoc a b0 x p0 p b) (lu '(NatOp mul) x y a)))
                                       (Imp H3 goal)))))))))))))
      (T (list (fa-e (fa-e (fa-e (fa-e (fa-e l z) s) p) a) b))
         (c `(imp (and (pr Nat ,x) (pr Nat ,y) (pr Nat ,z) ,(Add y z s) ,(Mul x s p) ,(Mul x y a) ,(Mul x z b)) ,(Add a b p)))))))

;; MulAssoc: Nat x & Nat y & Nat z & Mul(x,y,a) & Mul(a,z,p) & Mul(y,z,b) -> Mul(x,b,p)      x y z a p b = 0..5
(define ((phi-mulassoc x y) n)
  (let ([a (fresh-sym 'a)] [p (fresh-sym 'p)] [b (fresh-sym 'b)])
    `(all ,a (all ,p (all ,b (imp (and ,(Mul x y a) ,(Mul a n p) ,(Mul y n b)) ,(Mul x b p)))))))
(define (mulassoc!)
  (law! 'MulAssoc 6 '(IndMulAssoc) 2 phi-mulassoc (list (lambda () (kind-all! 'add) (kind-all! 'mul)) distl!)
    (lambda ()
      (define-values (x y z a p b) (values 0 1 2 3 4 5))
      (define H (c `(and (pr Nat ,x) (pr Nat ,y))))
      (define (exq P) (c (let ([q (fresh-sym 'q)]) `(ex ,q ,(P q)))))
      (define l (ind-proof H '(IndMulAssoc) (list x y) phi-mulassoc
                  (lambda (e He)
                    (under-all He (c ((phi-mulassoc x y) e)) 3
                      (lambda (vs HA) (match-define (list a p b) vs)
                        (T (list (lu '(NatOp mul) x y a) (lu '(Zinv mul) a e p) (lu '(Zinv mul) y e b) (lu '(Z mul) x e)
                                 (leib `(not ,(Mul x HOLE p)) b e) (leib `(not ,(Mul x e HOLE)) p e))
                           (Imp HA (c (Mul x b p)))))))
                  (lambda (n m Hm)
                    (under-all Hm (c ((phi-mulassoc x y) m)) 3
                      (lambda (vs HA) (match-define (list a p b) vs)
                        (define goal (c (Mul x b p)))
                        (obt HA (list (lu '(NatOp mul) x y a) (lu '(Sinv mul) a n m p)) (exq (lambda (q) `(and (pr Nat ,q) ,(Mul a n q) ,(Add q a p))))
                          (lambda (p0 _1 H1)
                            (obt H1 (list (lu '(Sinv mul) y n m b)) (exq (lambda (q) `(and (pr Nat ,q) ,(Mul y n q) ,(Add q y b))))
                              (lambda (b0 _2 H2)
                                (obt H2 (list (lu '(NatOp add) b0 y b) (lu '(Tot mul) x b)) (exq (lambda (q) `(and (pr Nat ,q) ,(Mul x b q))))
                                  (lambda (P _3 H3)
                                    (T (append (inst* (c ((phi-mulassoc x y) n)) (list a p0 b0))
                                               (list (lu 'DistL x b0 y b P p0 a) (lu '(Uq add) p0 a P p) (leib (Mul x b HOLE) P p)
                                                     (lu '(NatOp mul) x y a)))
                                       (Imp H3 goal)))))))))))))
      (T (list (fa-e (fa-e (fa-e (fa-e l z) a) p) b))
         (c `(imp (and (pr Nat ,x) (pr Nat ,y) (pr Nat ,z) ,(Mul x y a) ,(Mul a z p) ,(Mul y z b)) ,(Mul x b p)))))))

;; ======================================================================== closed forms
;; the universal closure of a law (its free variables 0..n-1)
(define (closed! key n)
  (define ck `(Closed ,key))
  (need ck
   (lambda ()
    (lemma! ck 0
     (lambda ()
       (define vs (for/list ([i n]) (fresh!)))
       (for/fold ([l (U (reg-index key) vs)]) ([v (reverse vs)]) (G l v)))))))

(define LAWS
  (list (list 'AddZL 2 addzl!) (list 'AddSL 5 addsl!) (list 'AddComm 3 addcomm!) (list 'AddAssoc 6 addassoc!)
        (list 'MulZL 2 mulzl!) (list 'MulSL 5 mulsl!) (list 'MulComm 3 mulcomm!) (list 'DistL 7 distl!) (list 'MulAssoc 6 mulassoc!)))
(define (all-laws!)
  (for ([e LAWS]) ((caddr e)))
  (for ([e LAWS]) (closed! (car e) (cadr e))))
