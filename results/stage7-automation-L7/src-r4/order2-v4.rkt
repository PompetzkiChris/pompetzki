#lang racket/base
;; order2-v4.rkt -- lane L7 round 2, item 2: order and cancellation on omega, from sigma1's Add and Mul and the laws of
;; omega-laws-v3.rkt. Le(x,y) := exists d (Nat d & Add(x,d,y)); Lt(x,y) := exists d (Nat d & not Emp(d) & Add(x,d,y)).
(require "l7core-v1.rkt" "omega-base-v1.rkt" "omega-kind-v5.rkt" "omega-laws-v3.rkt" racket/list racket/match)
(provide (all-defined-out))

(define (Le x y) (let ([d (fresh-sym 'd)]) `(ex ,d (and (pr Nat ,d) ,(Add x d y)))))
(define (Lt x y) (let ([d (fresh-sym 'd)]) `(ex ,d (and (pr Nat ,d) (not (pr Emp ,d)) ,(Add x d y)))))
(define (exq P) (c (let ([q (fresh-sym 'q)]) `(ex ,q ,(P q)))))
(define (tot-add x y) (lu '(Tot add) x y))           ; Nat x & Nat y -> exists z (Nat z & Add(x,y,z))
(define (tot-mul x y) (lu '(Tot mul) x y))
(define (ex-add x y) (exq (lambda (q) `(and (pr Nat ,q) ,(Add x y q)))))
(define (ex-mul x y) (exq (lambda (q) `(and (pr Nat ,q) ,(Mul x y q)))))
(define (base!) (kind-all! 'add) (kind-all! 'mul) (for ([e LAWS]) ((caddr e))))

;; NatCases: Nat(y) -> Emp(y) or exists p (Nat p & Suc(y,p))                     y = 0
(define (phi-cases) (lambda (n) `(or (pr Emp ,n) ,(let ([p (fresh-sym 'p)]) `(ex ,p (and (pr Nat ,p) (pr Suc ,n ,p)))))))
(define (natcases!)
  (law! 'NatCases 1 '(IndNatCases) 0 phi-cases (list base!)
    (lambda ()
      (define y 0)
      (define H (c `(pr Nat ,y)))
      (define phi (phi-cases))
      (define l (ind-proof H '(IndNatCases) '() phi-cases
                  (lambda (e He) (T '() (Imp He (c (phi e)))))
                  (lambda (n m Hm)
                    (define exn (c (let ([p (fresh-sym 'p)]) `(ex ,p (and (pr Nat ,p) (pr Suc ,m ,p))))))
                    (T (list (ex-i n exn)) (Imp Hm (c (phi m)))))))
      (T (list (fa-e* l y)) (c `(imp (pr Nat ,y) ,(phi y)))))))

;; AddCancelR: Nat x & Nat y & Nat z & Add(x,z,u) & Add(y,z,u) -> x = y          x y z u = 0..3
(define ((phi-cancel x y) n) (let ([u (fresh-sym 'u)]) `(all ,u (imp (and ,(Add x n u) ,(Add y n u)) (eq ,x ,y)))))
(define (addcancelr!)
  (law! 'AddCancelR 4 '(IndAddCancelR) 2 phi-cancel (list base!)
    (lambda ()
      (define-values (x y z u) (values 0 1 2 3))
      (define H (c `(and (pr Nat ,x) (pr Nat ,y))))
      (define l (ind-proof H '(IndAddCancelR) (list x y) phi-cancel
                  (lambda (e He)
                    (under-all He (c ((phi-cancel x y) e)) 1
                      (lambda (vs HA) (match-define (list u) vs)
                        (T (list (lu '(Zinv add) x e u) (lu '(Zinv add) y e u) (leib `(eq ,HOLE ,y) u x)) (Imp HA (c `(eq ,x ,y)))))))
                  (lambda (n m Hm)
                    (under-all Hm (c ((phi-cancel x y) m)) 1
                      (lambda (vs HA) (match-define (list u) vs)
                        (define goal (c `(eq ,x ,y)))
                        (obt HA (list (lu '(Sinv add) x n m u)) (exq (lambda (q) `(and (pr Nat ,q) ,(Add x n q) (pr Suc ,u ,q))))
                          (lambda (u0 _1 H1)
                            (obt H1 (list (lu '(Sinv add) y n m u)) (exq (lambda (q) `(and (pr Nat ,q) ,(Add y n q) (pr Suc ,u ,q))))
                              (lambda (u1 _2 H2)
                                (T (list (rs "L:SucInj" u u0 u1) (leib (Add x n HOLE) u0 u1) (inst (c ((phi-cancel x y) n)) u1))
                                   (Imp H2 goal)))))))))))
      (T (list (fa-e* (fa-e* l z) u)) (c `(imp (and (pr Nat ,x) (pr Nat ,y) (pr Nat ,z) ,(Add x z u) ,(Add y z u)) (eq ,x ,y)))))))

;; AddCancelL: Nat x & Nat y & Nat z & Add(z,x,u) & Add(z,y,u) -> x = y          x y z u = 0..3
(define (addcancell!)
  (need 'AddCancelL
   (lambda ()
    (addcancelr!)
    (lemma! 'AddCancelL 4
     (lambda ()
       (define-values (x y z u) (values 0 1 2 3))
       (T (list (lu 'AddComm z x u) (lu 'AddComm z y u) (lu 'AddCancelR x y z u))
          (c `(imp (and (pr Nat ,x) (pr Nat ,y) (pr Nat ,z) ,(Add z x u) ,(Add z y u)) (eq ,x ,y)))))))))

;; ZeroSum: Nat x & Nat y & Add(x,y,z) & Emp(z) -> Emp(x) & Emp(y)                x y z = 0..2
(define (zerosum!)
  (need 'ZeroSum
   (lambda ()
    (natcases!)
    (lemma! 'ZeroSum 3
     (lambda ()
       (define-values (x y z) (values 0 1 2))
       (define H0 (c `(and (pr Nat ,x) (pr Nat ,y) ,(Add x y z) (pr Emp ,z))))
       (define goal (c `(and (pr Emp ,x) (pr Emp ,y))))
       (define caseA (T (list (lu '(Zinv add) x y z) (leib `(pr Emp ,HOLE) z x)) (Imp H0 (Imp (c `(pr Emp ,y)) goal))))
       (define p (fresh!))
       (define Pp (c `(and (pr Nat ,p) (pr Suc ,y ,p))))
       (define H1 (Kf H0 Pp))
       (define inner (obt H1 (list (lu '(Sinv add) x p y z)) (exq (lambda (q) `(and (pr Nat ,q) ,(Add x p q) (pr Suc ,z ,q))))
                       (lambda (z0 _ H2) (T (list (rs "L:SucNe" z z0 z) (Y (Eqv z z))) (Imp H2 goal)))))
       (define caseB (ex-e p (T (list inner) (Imp Pp (Imp H0 goal)))))
       (T (list (lu 'NatCases y) caseA caseB) (Imp H0 goal)))))))

;; RComm: Nat p,a,b & Add(p,a,s) & Add(s,b,c) & Add(p,b,s2) & Add(s2,a,c2) -> c = c2      p a b s c s2 c2 = 0..6
(define (rcomm!)
  (need 'RComm
   (lambda ()
    (base!)
    (lemma! 'RComm 7
     (lambda ()
       (define-values (p a b s cc s2 c2) (values 0 1 2 3 4 5 6))
       (define H0 (c `(and (pr Nat ,p) (pr Nat ,a) (pr Nat ,b) ,(Add p a s) ,(Add s b cc) ,(Add p b s2) ,(Add s2 a c2))))
       (define goal (c `(eq ,cc ,c2)))
       (obt H0 (list (tot-add a b)) (ex-add a b)
         (lambda (w _ H1)
           (T (list (lu 'AddAssoc p a b s cc w) (lu 'AddComm a b w) (lu 'AddAssoc p b a s2 c2 w) (lu '(Uq add) p w cc c2))
              (Imp H1 goal)))))))))

;; AssocEq: Nat x,y,z & Add(x,y,s) & Add(s,z,c) & Add(y,z,t) & Add(x,t,c2) -> c = c2     x y z s c t c2 = 0..6
(define (assoceq!)
  (need 'AssocEq
   (lambda ()
    (base!)
    (lemma! 'AssocEq 7
     (lambda ()
       (define-values (x y z s cc t c2) (values 0 1 2 3 4 5 6))
       (T (list (lu 'AddAssoc x y z s cc t) (lu '(NatOp add) y z t) (lu '(Uq add) x t cc c2))
          (c `(imp (and (pr Nat ,x) (pr Nat ,y) (pr Nat ,z) ,(Add x y s) ,(Add s z cc) ,(Add y z t) ,(Add x t c2)) (eq ,cc ,c2)))))))))

;; ======================================================================== order
;; LeRefl: Nat x -> Le(x,x)
(define (lerefl!)
  (need 'LeRefl
   (lambda ()
    (base!) (natzero!)
    (lemma! 'LeRefl 1
     (lambda ()
       (define x 0)
       (define goal (c (Le x x)))
       (define H (c `(pr Nat ,x)))
       (obt H (list (U 'EmpEx '())) (c (let ([e (fresh-sym 'e)]) `(ex ,e (pr Emp ,e))))
         (lambda (o _ H1)
           (T (list (lu '(Z add) x o) (lu 'NatZero o) (ex-i o goal)) (Imp H1 goal)))))))))

;; LeTrans: Nat x,y,z & Le(x,y) & Le(y,z) -> Le(x,z)
(define (letrans!)
  (need 'LeTrans
   (lambda ()
    (base!)
    (lemma! 'LeTrans 3
     (lambda ()
       (define-values (x y z) (values 0 1 2))
       (define goal (c (Le x z)))
       (define H0 (c `(and (pr Nat ,x) (pr Nat ,y) (pr Nat ,z) ,(Le x y) ,(Le y z))))
       (obt H0 '() (c (Le x y))
         (lambda (d1 _1 H1)
           (obt H1 '() (c (Le y z))
             (lambda (d2 _2 H2)
               (obt H2 (list (tot-add d1 d2)) (ex-add d1 d2)
                 (lambda (d _3 H3)
                   (T (list (lu 'AddAssoc x d1 d2 y z d) (ex-i d goal)) (Imp H3 goal)))))))))))))

;; AddSelf: Nat x & Nat e & Add(x,e,x) -> Emp(e)
(define (addself!)
  (need 'AddSelf
   (lambda ()
    (addcancell!) (natzero!)
    (lemma! 'AddSelf 2
     (lambda ()
       (define-values (x e) (values 0 1))
       (define goal (c `(pr Emp ,e)))
       (define H0 (c `(and (pr Nat ,x) (pr Nat ,e) ,(Add x e x))))
       (obt H0 (list (U 'EmpEx '())) (c (let ([o (fresh-sym 'e)]) `(ex ,o (pr Emp ,o))))
         (lambda (o _ H1)
           (T (list (lu '(Z add) x o) (lu 'NatZero o) (lu 'AddCancelL e o x x) (leib `(not (pr Emp ,HOLE)) e o)) (Imp H1 goal)))))))))

;; LeAntisym: Nat x,y & Le(x,y) & Le(y,x) -> x = y
(define (leantisym!)
  (need 'LeAntisym
   (lambda ()
    (addself!) (zerosum!)
    (lemma! 'LeAntisym 2
     (lambda ()
       (define-values (x y) (values 0 1))
       (define goal (c `(eq ,x ,y)))
       (define H0 (c `(and (pr Nat ,x) (pr Nat ,y) ,(Le x y) ,(Le y x))))
       (obt H0 '() (c (Le x y))
         (lambda (d1 _1 H1)
           (obt H1 '() (c (Le y x))
             (lambda (d2 _2 H2)
               (obt H2 (list (tot-add d1 d2)) (ex-add d1 d2)
                 (lambda (d _3 H3)
                   (T (list (lu 'AddAssoc x d1 d2 y x d) (lu 'AddSelf x d) (lu 'ZeroSum d1 d2 d) (lu '(Zinv add) x d1 y)
                            (rs "Z:EqSym" y x))
                      (Imp H3 goal)))))))))))))

;; (v4: the statement of LeTotal unquotes its formula. v3: LeAntisym ends with EqSym. v1 used Leibniz the wrong way round in AddSelf and stopped in LtIrrefl; v2 = v1's lemmas up to LeAntisym with that
;;  fix, then the lemmas below.)

;; LtIrrefl: Nat x -> not Lt(x,x)
(define (ltirrefl!)
  (need 'LtIrrefl
   (lambda ()
    (addself!)
    (lemma! 'LtIrrefl 1
     (lambda ()
       (define x 0)
       (define H0 (c `(and (pr Nat ,x) ,(Lt x x))))
       (define bad (Neg (Eqv x x)))
       (define l (obt H0 '() (c (Lt x x)) (lambda (d _ H1) (T (list (lu 'AddSelf x d)) (Imp H1 bad)))))
       (T (list l (Y (Eqv x x))) (c `(imp (pr Nat ,x) (not ,(Lt x x))))))))))

;; LeSucc: Nat n & Suc(m,n) -> Le(n,m)
(define (lesucc!)
  (need 'LeSucc
   (lambda ()
    (base!) (natzero!)
    (lemma! 'LeSucc 2
     (lambda ()
       (define-values (n m) (values 0 1))
       (define goal (c (Le n m)))
       (define H0 (c `(and (pr Nat ,n) (pr Suc ,m ,n))))
       (obt H0 (list (U 'EmpEx '())) (c (let ([e (fresh-sym 'e)]) `(ex ,e (pr Emp ,e))))
         (lambda (o _1 H1)
           (obt H1 (list (ru "H:SucEx" o)) (c (let ([s (fresh-sym 's)]) `(ex ,s (pr Suc ,s ,o))))
             (lambda (one _2 H2)
               (T (list (lu '(Z add) n o) (lu 'NatZero o) (lu '(S add) n o n one m) (ru "H:NatSuc" o one) (ex-i one goal))
                  (Imp H2 goal)))))))))))

;; LeTotal: Nat x & Nat y -> Le(x,y) or Le(y,x)                 x y = 0 1; induction on x, parameter y
(define ((phi-total y) n) `(or ,(Le n y) ,(Le y n)))
(define (letotal!)
  (law! 'LeTotal 2 '(IndLeTotal) 1 phi-total (list base! natcases! lesucc! letrans!)
    (lambda ()
      (define-values (x y) (values 0 1))
      (define H (c `(pr Nat ,y)))
      (define l
        (ind-proof H '(IndLeTotal) (list y) phi-total
          (lambda (e He) (T (list (lu 'AddZL e y) (ex-i y (c (Le e y)))) (Imp He (c ((phi-total y) e)))))
          (lambda (n m Hm)
            (define goal (c ((phi-total y) m)))
            (define caseA (T (list (lu 'LeSucc n m) (lu 'LeTrans y n m) (ru "H:NatSuc" n m)) (Imp Hm (Imp (c (Le y n)) goal))))
            (define HB (Kf Hm (c (Le n y))))
            (define inB
              (obt HB '() (c (Le n y))
                (lambda (d _1 Hd)
                  (define B1 (T (list (lu '(Zinv add) n d y) (lu 'LeSucc n m) (leib `(not ,(Le HOLE m)) y n)) (Imp Hd (Imp (c `(pr Emp ,d)) goal))))
                  (define d0 (fresh!))
                  (define P0 (c `(and (pr Nat ,d0) (pr Suc ,d ,d0))))
                  (define H0 (Kf Hd P0))
                  (define inner
                    (obt H0 (list (tot-add n d0)) (ex-add n d0)
                      (lambda (q _2 H1)
                        (obt H1 (list (ru "H:SucEx" q)) (c (let ([s (fresh-sym 's)]) `(ex ,s (pr Suc ,s ,q))))
                          (lambda (y2 _3 H2)
                            (define ex-m (c (Le m y)))
                            (T (list (lu '(S add) n d0 q d y2) (lu '(Uq add) n d y2 y) (leib `(pr Suc ,HOLE ,q) y2 y)
                                     (lu 'AddSL n d0 m q y) (ex-i d0 ex-m))
                               (Imp H2 goal)))))))
                  (define B2 (ex-e d0 (T (list inner) (Imp P0 (Imp Hd goal)))))
                  (T (list (lu 'NatCases d) B1 B2) (Imp Hd goal)))))
            (define caseB (T (list inB) (Imp Hm (Imp (c (Le n y)) goal))))
            (T (list caseA caseB) (Imp Hm goal)))))
      (T (list (fa-e* l x)) (c `(imp (and (pr Nat ,x) (pr Nat ,y)) ,((phi-total y) x)))))))

;; LeAddMono: Nat x,y,z & Le(x,y) & Add(x,z,p) & Add(y,z,q) -> Le(p,q)          x y z p q = 0..4
(define (leaddmono!)
  (need 'LeAddMono
   (lambda ()
    (base!) (rcomm!)
    (lemma! 'LeAddMono 5
     (lambda ()
       (define-values (x y z p q) (values 0 1 2 3 4))
       (define goal (c (Le p q)))
       (define H0 (c `(and (pr Nat ,x) (pr Nat ,y) (pr Nat ,z) ,(Le x y) ,(Add x z p) ,(Add y z q))))
       (obt H0 '() (c (Le x y))
         (lambda (d _1 H1)
           (obt H1 (list (lu '(NatOp add) x z p) (tot-add p d)) (ex-add p d)
             (lambda (t _2 H2)
               (T (list (lu 'RComm x z d p t y q) (leib (Add p d HOLE) t q) (ex-i d goal)) (Imp H2 goal)))))))))))

;; LeAddCancel: Nat x,y,z & Add(x,z,p) & Add(y,z,q) & Le(p,q) -> Le(x,y)        x y z p q = 0..4
(define (leaddcancel!)
  (need 'LeAddCancel
   (lambda ()
    (base!) (rcomm!) (addcancelr!)
    (lemma! 'LeAddCancel 5
     (lambda ()
       (define-values (x y z p q) (values 0 1 2 3 4))
       (define goal (c (Le x y)))
       (define H0 (c `(and (pr Nat ,x) (pr Nat ,y) (pr Nat ,z) ,(Add x z p) ,(Add y z q) ,(Le p q))))
       (obt H0 '() (c (Le p q))
         (lambda (d _1 H1)
           (obt H1 (list (tot-add x d)) (ex-add x d)
             (lambda (t _2 H2)
               (obt H2 (list (tot-add t z)) (ex-add t z)
                 (lambda (t2 _3 H3)
                   (T (list (lu 'RComm x d z t t2 p q) (leib (Add t z HOLE) t2 q) (lu 'AddCancelR t y z q)
                            (leib (Add x d HOLE) t y) (ex-i d goal))
                      (Imp H3 goal)))))))))))))

;; ZeroProd: Nat d & Nat z & Mul(d,z,p) & Emp(p) & not Emp(z) -> Emp(d)          d z p = 0..2
(define (zeroprod!)
  (need 'ZeroProd
   (lambda ()
    (base!) (natcases!) (zerosum!)
    (lemma! 'ZeroProd 3
     (lambda ()
       (define-values (d z p) (values 0 1 2))
       (define goal (c `(pr Emp ,d)))
       (define H0 (c `(and (pr Nat ,d) (pr Nat ,z) ,(Mul d z p) (pr Emp ,p) (not (pr Emp ,z)))))
       (define d0 (fresh!))
       (define P0 (c `(and (pr Nat ,d0) (pr Suc ,d ,d0))))
       (define H1 (Kf H0 P0))
       (define inner
         (obt H1 (list (tot-mul d0 z)) (ex-mul d0 z)
           (lambda (q _1 H2)
             (obt H2 (list (tot-add q z)) (ex-add q z)
               (lambda (p2 _2 H3)
                 (T (list (lu 'MulSL d0 z d q p2) (lu '(Uq mul) d z p p2) (leib `(not ,(Add q z HOLE)) p p2) (lu 'ZeroSum q z p))
                    (Imp H3 goal)))))))
       (define B (ex-e d0 (T (list inner) (Imp P0 (Imp H0 goal)))))
       (T (list (lu 'NatCases d) B) (Imp H0 goal)))))))

;; MulCancel1: Nat x,y,z & not Emp(z) & Le(x,y) & Mul(x,z,u) & Mul(y,z,u) -> x = y          x y z u = 0..3
(define (mulcancel1!)
  (need 'MulCancel1
   (lambda ()
    (base!) (addself!) (zeroprod!)
    (lemma! 'MulCancel1 4
     (lambda ()
       (define-values (x y z u) (values 0 1 2 3))
       (define goal (c `(eq ,x ,y)))
       (define H0 (c `(and (pr Nat ,x) (pr Nat ,y) (pr Nat ,z) (not (pr Emp ,z)) ,(Le x y) ,(Mul x z u) ,(Mul y z u))))
       (obt H0 '() (c (Le x y))
         (lambda (d _1 H1)
           (obt H1 (list (tot-mul z d)) (ex-mul z d)
             (lambda (b _2 H2)
               (T (list (lu 'MulComm y z u) (lu 'MulComm x z u) (lu 'DistL z x d y u u b) (lu '(NatOp mul) x z u)
                        (lu 'AddSelf u b) (lu 'MulComm z d b) (lu 'ZeroProd d z b) (lu '(Zinv add) x d y) (rs "Z:EqSym" y x))
                  (Imp H2 goal)))))))))))

;; MulCancel: Nat x,y,z & not Emp(z) & Mul(x,z,u) & Mul(y,z,u) -> x = y          x y z u = 0..3
(define (mulcancel!)
  (need 'MulCancel
   (lambda ()
    (letotal!) (mulcancel1!)
    (lemma! 'MulCancel 4
     (lambda ()
       (define-values (x y z u) (values 0 1 2 3))
       (T (list (lu 'LeTotal x y) (lu 'MulCancel1 x y z u) (lu 'MulCancel1 y x z u) (rs "Z:EqSym" y x))
          (c `(imp (and (pr Nat ,x) (pr Nat ,y) (pr Nat ,z) (not (pr Emp ,z)) ,(Mul x z u) ,(Mul y z u)) (eq ,x ,y)))))))))

(define ORDER-LEMMAS
  (list (list 'NatCases 1 natcases!) (list 'AddCancelR 4 addcancelr!) (list 'AddCancelL 4 addcancell!) (list 'ZeroSum 3 zerosum!)
        (list 'RComm 7 rcomm!) (list 'AssocEq 7 assoceq!) (list 'LeRefl 1 lerefl!) (list 'LeTrans 3 letrans!)
        (list 'AddSelf 2 addself!) (list 'LeAntisym 2 leantisym!) (list 'LtIrrefl 1 ltirrefl!) (list 'LeSucc 2 lesucc!)
        (list 'LeTotal 2 letotal!) (list 'LeAddMono 5 leaddmono!) (list 'LeAddCancel 5 leaddcancel!)
        (list 'ZeroProd 3 zeroprod!) (list 'MulCancel1 4 mulcancel1!) (list 'MulCancel 4 mulcancel!)))
