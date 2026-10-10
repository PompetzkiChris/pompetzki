#lang racket/base
;; omega-kind-v5.rkt -- lane L7, item 4: the recursion lemmas of Add and Mul (sigma1's definitions) for all of omega.
;; (v1 stopped in the middle of Step; v2 lacked one closing parenthesis in kuq! and had one too many in ks!; v3 fixed kuq!, v4 ks!;
;;  v5 adds the line n in y to the last tautology step of Uq.)
(require "l7core-v1.rkt" "omega-base-v1.rkt" racket/list racket/match)
(provide (all-defined-out))

;; ---- context elimination of an existential
;; H: core context; ls: lines from which H -> ex is a tautology; ex: core existential exists x P;
;; k: (v Pv H2) -> line H2 -> G, H2 = H & P(v).  Result: the line H -> G.
(define (obt H ls ex k)
  (define body (match ex [(list 'N (list 'A (list 'N b))) b] [_ (error 'obt "not an existential: ~a" (show ex))]))
  (define v (fresh!))
  (define Pv (ren (scons v sid) body))
  (define H2 (Kf H Pv))
  (define l (k v Pv H2))
  (define G (match (line l) [(list 'I h g) #:when (equal? h H2) g] [f (error 'obt "line is not H2 -> G: ~a" (show f))]))
  (define l1 (T (list l) (Imp Pv (Imp H G))))
  (define l2 (ex-e v l1))
  (T (cons l2 ls) (Imp H G)))
;; H -> forall^n M by opening F (a core forall formula) under the context H
(define (all-under H F n k)
  (define-values (vs Mx) (open-all F n))
  (close-all (k vs Mx) vs))
(define (imp-parts f) (match f [(list 'I a b) (values a b)]))
(define (ex-of f) (match f [(list 'N (list 'A (list 'N b))) f]))

(define (uq-hyps kind x y) (if (eq? kind 'add) (list (Nat y)) (list (Nat x) (Nat y))))

;; ======================================================================== Base: Emp(o) -> exists f (Body(f,x,o,z0) & Dm(f,o))     x o = 0 1
(define (kbase! kind)
  (define key `(Base ,kind))
  (need key
   (lambda ()
    (sngfun!)
    (lemma! key 2
     (lambda ()
       (define-values (x o) (values 0 1))
       (define z0 (z0of kind x o))
       (define p (fresh!)) (define f (fresh!))
       (define hypc (c `(and (pr Emp ,o) (pr Opr ,p ,o ,z0) (pr Sng ,f ,p))))
       (define (sf i a) (lu 'SngFun f p o z0 i a))
       (define parts (fin-parts kind f x o z0))
       (define fncd (unfold 'Fnc (list f)))
       (define fnc (T (list fncd (all-under hypc (def-body fncd) 3
                                           (lambda (vs Mx) (match-define (list i a b) vs)
                                             (T (list (sf i a) (sf i b) (leib `(eq ,HOLE ,b) z0 a)) (Imp hypc Mx)))))
                      (Imp hypc (c `(pr Fnc ,f)))))
       (define zero (all-under hypc (c (list-ref parts 1)) 1
                               (lambda (vs Mx) (match-define (list e) vs)
                                 (define val (if (eq? kind 'add) x e))
                                 (T (list (sf e val) (rs "L:EmpUq" o e) (Y (Eqv x x))) (Imp hypc Mx)))))
       (define dom (all-under hypc (c (list-ref parts 2)) 1
                              (lambda (vs Mx) (T (list (rs "L:EmpNo" o (car vs))) (Imp hypc Mx)))))
       (define st (all-under hypc (c (list-ref parts 3)) 4
                             (lambda (vs Mx) (T (list (rs "L:EmpNo" o (car vs))) (Imp hypc Mx)))))
       (define app (T (list (sf o z0) (Y (Eqv o o)) (Y (Eqv z0 z0))) (Imp hypc (c (list-ref parts 4)))))
       (define dm (all-under hypc (c (Dm f o)) 2
                             (lambda (vs Mx) (match-define (list i a) vs)
                               (T (list (sf i a) (rs "Z:EqSym" o i)) (Imp hypc Mx)))))
       (define G (c (let ([F (fresh-sym 'f)]) `(ex ,F (and ,(Body kind F x o z0) ,(Dm F o))))))
       (define l1 (T (list fnc zero dom st app dm (ex-i f G)) (Imp (c `(pr Sng ,f ,p)) (Imp (c `(and (pr Emp ,o) (pr Opr ,p ,o ,z0))) G))))
       (define l2 (M (rs "Z:SngEx" p) (ex-e f l1)))
       (define l3 (T (list l2) (Imp (c `(pr Opr ,p ,o ,z0)) (Imp (c `(pr Emp ,o)) G))))
       (M (rs "Z:OprEx" o z0) (ex-e p l3)))))))

;; ======================================================================== Step
;; Body(f,x,y,z) & Dm(f,y) & Suc(y2,y) & C(z,z2) & Opr(p,y2,z2) & Un(g,f,p) -> Body(g,x,y2,z2) & Dm(g,y2)
;; x y z f y2 z2 p g = 0..7
(define (kstep! kind)
  (define key `(Step ,kind))
  (need key
   (lambda ()
    (unfun!)
    (lemma! key 8
     (lambda ()
       (define-values (x y z f y2 z2 p g) (values 0 1 2 3 4 5 6 7))
       (define partsF (fin-parts kind f x y z))
       (define partsG (fin-parts kind g x y2 z2))
       (define hypc (c `(and ,(Body kind f x y z) ,(Dm f y) (pr Suc ,y2 ,y) ,(Cst kind x z z2) (pr Opr ,p ,y2 ,z2) ,(Un g f p))))
       (define (H> d) (Imp hypc (c d)))
       (define (uf i a) (lu 'UnFun g f p y2 z2 i a))
       (define sucd (unfold 'Suc (list y2 y)))
       (define sucB (def-body sucd))
       (define (sucat i) (list sucd (inst sucB i)))
       (define F1 (T (append (sucat y) (list (Y (Eqv y y)))) (H> `(in ,y ,y2))))
       (define F2 (T (list F1 (rs "L:NoTwo" y y2)) (H> `(not (in ,y2 ,y)))))
       (define F3 (T (list F1 (leib `(in ,y ,HOLE) y2 y) (rs "L:NoSelf" y)) (H> `(not (eq ,y2 ,y)))))
       (define Dmf (c (Dm f y)))
       (define (notdom a) (T (append (inst* Dmf (list y2 a)) (list F2 F3)) (H> `(not (pr App ,f ,y2 ,a)))))
       ;; Fnc(g)
       (define fncd (unfold 'Fnc (list g)))
       (define fnc
         (T (list fncd
                  (all-under hypc (def-body fncd) 3
                             (lambda (vs Mx) (match-define (list i a b) vs)
                               (T (list (uf i a) (uf i b) (rs "Z:FncApp" f i a b) (notdom a) (notdom b)
                                        (leib `(not (pr App ,f ,HOLE ,a)) y2 i) (leib `(not (pr App ,f ,HOLE ,b)) y2 i)
                                        (leib `(eq ,HOLE ,b) z2 a))
                                  (Imp hypc Mx)))))
            (H> `(pr Fnc ,g))))
       ;; the value at 0
       (define zero (all-under hypc (c (list-ref partsG 1)) 1
                               (lambda (vs Mx) (match-define (list e) vs)
                                 (define val (if (eq? kind 'add) x e))
                                 (T (list (inst (c (list-ref partsF 1)) e) (uf e val)) (Imp hypc Mx)))))
       ;; defined on y2
       (define dom
         (all-under hypc (c (list-ref partsG 2)) 1
                    (lambda (vs Mx) (match-define (list i) vs)
                      (define exg (c (let ([a (fresh-sym 'a)]) `(ex ,a (pr App ,g ,i ,a)))))
                      (define a (fresh!))
                      (define c1 (T (list (uf i a) (ex-i a exg)) (Imp (c `(pr App ,f ,i ,a)) (Imp hypc exg))))
                      (define c2 (ex-e a c1))
                      (T (append (sucat i)
                                 (list (inst (c (list-ref partsF 2)) i) c2 (uf y z) (leib `(not (pr App ,g ,HOLE ,z)) i y) (ex-i z exg)))
                         (Imp hypc Mx)))))
       ;; the step
       (define st
         (all-under hypc (c (list-ref partsG 3)) 4
                    (lambda (vs Mx) (match-define (list i j a b) vs)
                      (define common (append (sucat i) (list (uf i a) (uf j b))))
                      (define caseA
                        (T (append common
                                   (list (leib `(not (in ,HOLE ,y)) y2 i) F2
                                         (leib `(not (pr Suc ,HOLE ,i)) y2 j) (rs "L:SucInj" y2 y i)
                                         (leib `(not (in ,HOLE ,y)) y i) (rs "L:NoSelf" y))
                                   (inst* (c (list-ref partsF 3)) (list i j a b)))
                           (Imp hypc (Imp (c `(in ,i ,y)) Mx))))
                      (define caseB
                        (T (append common
                                   (list (leib `(not (eq ,HOLE ,y)) y2 i) F3
                                         (leib `(pr App ,f ,HOLE ,a) i y) (rs "Z:FncApp" f y z a)
                                         (leib `(pr Suc ,j ,HOLE) i y) (rs "L:SucUq" j y2 y)
                                         (leib `(pr App ,f ,HOLE ,b) j y2) (notdom b)
                                         (leib (Cst kind x HOLE z2) z a) (leib (Cst kind x a HOLE) z2 b)))
                           (Imp hypc (Imp (c `(eq ,i ,y)) Mx))))
                      (T (append (sucat i) (list caseA caseB)) (Imp hypc Mx)))))
       (define app (T (list (uf y2 z2) (Y (Eqv y2 y2)) (Y (Eqv z2 z2))) (H> (list-ref partsG 4))))
       (define dm (all-under hypc (c (Dm g y2)) 2
                             (lambda (vs Mx) (match-define (list i a) vs)
                               (T (append (list (uf i a) (rs "Z:EqSym" y2 i)) (inst* Dmf (list i a)) (sucat i)) (Imp hypc Mx)))))
       (T (list fnc zero dom st app dm) (H> `(and ,(Body kind g x y2 z2) ,(Dm g y2)))))))))

;; ======================================================================== Ex: forall y (Nat y -> forall x (Nat x -> exists z (Nat z & exists f (Body(f,x,y,z) & Dm(f,y)))))
(define ((ex-phi kind) yy)
  (define xx (fresh-sym 'x)) (define zz (fresh-sym 'z)) (define ff (fresh-sym 'f))
  `(all ,xx (imp (pr Nat ,xx) (ex ,zz (and (pr Nat ,zz) (ex ,ff (and ,(Body kind ff xx yy zz) ,(Dm ff yy))))))))
(define (kex! kind)
  (define key `(Ex ,kind))
  (need key
   (lambda ()
    (kbase! kind) (kstep! kind) (natzero!)
    (when (eq? kind 'mul) (ktot! 'add))
    (define phi (ex-phi kind))
    (ind! `(IndEx ,kind) 0 phi)
    (lemma! key 0
     (lambda ()
       ;; base: forall o (Emp o -> phi o)
       (define o (fresh!))
       (define b1 (all-under (c `(pr Emp ,o)) (c (phi o)) 1
                             (lambda (vs Mx) (match-define (list x) vs)
                               (define-values (nx G) (imp-parts Mx))
                               (define z0 (z0of kind x o))
                               (T (list (lu `(Base ,kind) x o) (lu 'NatZero o) (ex-i z0 G)) (Imp (c `(pr Emp ,o)) Mx)))))
       (define base (G b1 o))
       ;; step: forall n (Nat n -> (phi n -> forall m (Suc(m,n) -> phi m)))
       (define n (fresh!)) (define m (fresh!))
       (define Hsc (c `(and (pr Nat ,n) ,(phi n) (pr Suc ,m ,n))))
       (define s1
         (all-under Hsc (c (phi m)) 1
                    (lambda (vs Mx) (match-define (list x) vs)
                      (define-values (nx Gm) (imp-parts Mx))
                      (define H1 (Kf Hsc nx))
                      (define E1 (inst (c (phi n)) x))
                      (define-values (_a E1r) (imp-parts (line E1)))
                      (define-values (_b exz) (imp-parts E1r))
                      (define l
                        (obt H1 (list E1) exz
                             (lambda (z Pz H2)
                               (define exf (match Pz [(list 'N (list 'I _ (list 'N e))) e]))
                               (obt H2 '() exf
                                    (lambda (f Qf H3)
                                      (define (cont z2 H4 natz2)
                                        (obt H4 (list (rs "Z:OprEx" m z2)) (c (let ([pp (fresh-sym 'p)]) `(ex ,pp (pr Opr ,pp ,m ,z2))))
                                             (lambda (p _p H5)
                                               (obt H5 (list (ru "K:AddEx" f p)) (c (let ([gg (fresh-sym 'g)]) `(ex ,gg ,(Un gg f p))))
                                                    (lambda (g _g H6)
                                                      (define exg (c (let ([gg (fresh-sym 'g)]) `(ex ,gg (and ,(Body kind gg x m z2) ,(Dm gg m))))))
                                                      (T (append (list (lu `(Step ,kind) x n z f m z2 p g) (ex-i g exg) (ex-i z2 Gm)) natz2)
                                                         (Imp H6 Gm)))))))
                                      (if (eq? kind 'add)
                                          (obt H3 (list (ru "H:SucEx" z)) (c (let ([zz (fresh-sym 'z)]) `(ex ,zz (pr Suc ,zz ,z))))
                                               (lambda (z2 _r H4) (cont z2 H4 (list (ru "H:NatSuc" z z2)))))
                                          (obt H3 (list (lu '(Tot add) z x)) (c (let ([zz (fresh-sym 'z)]) `(ex ,zz (and (pr Nat ,zz) ,(add-f z x zz)))))
                                               (lambda (z2 _r H4) (cont z2 H4 '())))))))))
                      (T (list l) (Imp Hsc Mx)))))
       (define s2 (T (list s1) (Imp (c `(and (pr Nat ,n) ,(phi n))) (c `(imp (pr Suc ,m ,n) ,(phi m))))))
       (define s3 (fa-i m s2))
       (define s4 (T (list s3) (c (let ([mm (fresh-sym 'm)]) `(imp (pr Nat ,n) (imp ,(phi n) (all ,mm (imp (pr Suc ,mm ,n) ,(phi mm)))))))))
       (define step (G s4 n))
       (T (list base step (U `(IndEx ,kind) '())) (c (ind-C phi))))))))

;; ======================================================================== Tot: Nat x & Nat y -> exists z (Nat z & Op(x,y,z))       x y = 0 1
(define (ktot! kind)
  (define key `(Tot ,kind))
  (need key
   (lambda ()
    (kex! kind)
    (lemma! key 2
     (lambda ()
       (define-values (x y) (values 0 1))
       (define H (c `(and (pr Nat ,x) (pr Nat ,y))))
       (define e2 (fa-e (fa-e (U `(Ex ,kind) '()) y) x))
       (define-values (_a r1) (imp-parts (line e2)))
       (define-values (_b exz) (imp-parts r1))
       (define goal (c (let ([zz (fresh-sym 'z)]) `(ex ,zz (and (pr Nat ,zz) ,(Op kind x y zz))))))
       (obt H (list e2) exz
            (lambda (z Pz H2)
              (define exf (match Pz [(list 'N (list 'I _ (list 'N e))) e]))
              (obt H2 '() exf
                   (lambda (f Qf H3)
                     (T (list (ex-i f (c (Op kind x y z))) (ex-i z goal)) (Imp H3 goal)))))))))))

;; ======================================================================== Uq: [Nat x] & Nat y & Op(x,y,z1) & Op(x,y,z2) -> z1 = z2      x y z1 z2 = 0..3
(define ((uq-psi y f g) kk)
  (define aa (fresh-sym 'a)) (define bb (fresh-sym 'b))
  `(imp (or (in ,kk ,y) (eq ,kk ,y)) (all ,aa (all ,bb (imp (and (pr App ,f ,kk ,aa) (pr App ,g ,kk ,bb)) (eq ,aa ,bb))))))
(define (kuq! kind)
  (define key `(Uq ,kind))
  (need key
   (lambda ()
    (when (eq? kind 'mul) (kuq! 'add))
    (nattr!)
    (ind! `(IndUq ,kind) 3 (uq-psi 0 1 2))
    (lemma! key 4
     (lambda ()
       (define-values (x y z1 z2) (values 0 1 2 3))
       (define H0 (c `(and ,@(uq-hyps kind x y) ,(Op kind x y z1) ,(Op kind x y z2))))
       (obt H0 '() (c (Op kind x y z1))
         (lambda (f Pf H1)
           (obt H1 '() (c (Op kind x y z2))
             (lambda (g Pg H2)
               (define psi (uq-psi y f g))
               (define partsF (fin-parts kind f x y z1))
               (define partsG (fin-parts kind g x y z2))
               ;; base
               (define bl
                 (all-under H2 (c (ind-B psi)) 1
                   (lambda (vs Mx) (match-define (list o) vs)
                     (define-values (eo r) (imp-parts Mx))
                     (define-values (oy ALL) (imp-parts r))
                     (define Hb (Kf H2 (Kf eo oy)))
                     (define v0 (z0of kind x o))
                     (define inner
                       (all-under Hb ALL 2
                         (lambda (vs2 Mx2) (match-define (list a b) vs2)
                           (T (list (inst (c (list-ref partsF 1)) o) (inst (c (list-ref partsG 1)) o)
                                    (rs "Z:FncApp" f o v0 a) (rs "Z:FncApp" g o v0 b) (leib `(eq ,HOLE ,b) v0 a))
                              (Imp Hb Mx2)))))
                     (T (list inner) (Imp H2 Mx)))))
               ;; step
               (define sl
                 (all-under H2 (c (ind-S psi)) 1
                   (lambda (vs Mx) (match-define (list n) vs)
                     (define-values (natn r) (imp-parts Mx))
                     (define-values (psin ALLM) (imp-parts r))
                     (define Hn (Kf H2 (Kf natn psin)))
                     (define-values (_y ALLn) (imp-parts psin))
                     (define l
                       (all-under Hn ALLM 1
                         (lambda (vs2 Mx2) (match-define (list m) vs2)
                           (define-values (sucmn r2) (imp-parts Mx2))
                           (define-values (my ALLm) (imp-parts r2))
                           (define Hm (Kf Hn (Kf sucmn my)))
                           (define N1 (T (list (U 'SucIn (list m n)) (lu 'NatTr y n m) (leib `(in ,n ,HOLE) m y)) (Imp Hm (c `(in ,n ,y)))))
                           (define A1 (T (list N1) (Imp Hm ALLn)))
                           (define exfa (c (let ([a (fresh-sym 'a)]) `(ex ,a (pr App ,f ,n ,a)))))
                           (define exga (c (let ([a (fresh-sym 'a)]) `(ex ,a (pr App ,g ,n ,a)))))
                           (define ln
                             (obt Hm (list N1 (inst (c (list-ref partsF 2)) n)) exfa
                               (lambda (a1 _1 Ha)
                                 (obt Ha (list N1 (inst (c (list-ref partsG 2)) n)) exga
                                   (lambda (b1 _2 Hb)
                                     (all-under Hb ALLm 2
                                       (lambda (vs3 Mx3) (match-define (list a b) vs3)
                                         (define cu
                                           (if (eq? kind 'add)
                                               (list (leib `(not (pr Suc ,b ,HOLE)) a1 b1) (rs "L:SucUq" a b a1))
                                               (list (leib `(not ,(add-f HOLE x b)) a1 b1) (lu '(Uq add) a1 x a b))))
                                         (T (append (list A1 N1) (inst* ALLn (list a1 b1))
                                                    (inst* (c (list-ref partsF 3)) (list n m a1 a))
                                                    (inst* (c (list-ref partsG 3)) (list n m b1 b)) cu)
                                            (Imp Hb Mx3)))))))))
                           (T (list ln) (Imp Hn Mx2)))))
                     (T (list l) (Imp H2 Mx)))))
               (define fin1 (T (list bl sl (U `(IndUq ,kind) (list y f g))) (Imp H2 (c (ind-C psi)))))
               (define fin2 (fa-e fin1 y))
               (define ALLy (let-values ([(a b) (imp-parts (c (psi y)))]) b))
               (define fin3 (T (list fin2 (Y (Eqv y y))) (Imp H2 ALLy)))
               (define fin5 (fa-e (fa-e fin3 z1) z2))
               (T (list fin5) (Imp H2 (c `(eq ,z1 ,z2)))))))))))))

;; ======================================================================== S: Nat x & Nat y & Op(x,y,z) & Suc(y2,y) & C(z,z2) -> Op(x,y2,z2)   x y z y2 z2 = 0..4
(define (ks! kind)
  (define key `(S ,kind))
  (need key
   (lambda ()
    (kex! kind) (kuq! kind) (kstep! kind)
    (lemma! key 5
     (lambda ()
       (define-values (x y z y2 z2) (values 0 1 2 3 4))
       (define H0 (c `(and (pr Nat ,x) (pr Nat ,y) ,(Op kind x y z) (pr Suc ,y2 ,y) ,(Cst kind x z z2))))
       (define goal (c (Op kind x y2 z2)))
       (define e2 (fa-e (fa-e (U `(Ex ,kind) '()) y) x))
       (define-values (_a r1) (imp-parts (line e2)))
       (define-values (_b exz) (imp-parts r1))
       (obt H0 (list e2) exz
         (lambda (z0 Pz H1)
           (define exf (match Pz [(list 'N (list 'I _ (list 'N e))) e]))
           (obt H1 '() exf
             (lambda (f Qf H2)
               (define pre (list (lu `(Uq ,kind) x y z z0) (ex-i f (c (Op kind x y z0))) (leib (Cst kind x HOLE z2) z z0)))
               (obt H2 (list (rs "Z:OprEx" y2 z2)) (c (let ([pp (fresh-sym 'p)]) `(ex ,pp (pr Opr ,pp ,y2 ,z2))))
                 (lambda (p _p H3)
                   (obt H3 (list (ru "K:AddEx" f p)) (c (let ([gg (fresh-sym 'g)]) `(ex ,gg ,(Un gg f p))))
                     (lambda (g _g H4)
                       (T (append pre (list (lu `(Step ,kind) x y z0 f y2 z2 p g) (ex-i g goal))) (Imp H4 goal)))))))))))))))

;; ======================================================================== Z: Emp(o) -> Op(x,o,z0)         x o = 0 1
(define (kz! kind)
  (define key `(Z ,kind))
  (need key
   (lambda ()
    (kbase! kind)
    (lemma! key 2
     (lambda ()
       (define-values (x o) (values 0 1))
       (define z0 (z0of kind x o))
       (define goal (c (Op kind x o z0)))
       (define exf (c (let ([F (fresh-sym 'f)]) `(ex ,F (and ,(Body kind F x o z0) ,(Dm F o))))))
       (obt (c `(pr Emp ,o)) (list (lu `(Base ,kind) x o)) exf
            (lambda (f Q H1) (T (list (ex-i f goal)) (Imp H1 goal)))))))))

;; Zinv: Nat x & Emp(o) & Op(x,o,z) -> z = z0          x o z = 0..2
(define (kzinv! kind)
  (define key `(Zinv ,kind))
  (need key
   (lambda ()
    (kz! kind) (kuq! kind) (natzero!)
    (lemma! key 3
     (lambda ()
       (define-values (x o z) (values 0 1 2))
       (define z0 (z0of kind x o))
       (T (list (lu `(Z ,kind) x o) (lu 'NatZero o) (lu `(Uq ,kind) x o z z0))
          (c `(imp (and (pr Nat ,x) (pr Emp ,o) ,(Op kind x o z)) (eq ,z ,z0)))))))))

;; Sinv: Nat x & Nat y & Suc(y2,y) & Op(x,y2,z2) -> exists z (Nat z & Op(x,y,z) & C(z,z2))     x y y2 z2 = 0..3
(define (ksinv! kind)
  (define key `(Sinv ,kind))
  (need key
   (lambda ()
    (ktot! kind) (ks! kind) (kuq! kind)
    (when (eq? kind 'mul) (ktot! 'add))
    (lemma! key 4
     (lambda ()
       (define-values (x y y2 z2) (values 0 1 2 3))
       (define H0 (c `(and (pr Nat ,x) (pr Nat ,y) (pr Suc ,y2 ,y) ,(Op kind x y2 z2))))
       (define goal (c (let ([zz (fresh-sym 'z)]) `(ex ,zz (and (pr Nat ,zz) ,(Op kind x y zz) ,(Cst kind x zz z2))))))
       (obt H0 (list (lu `(Tot ,kind) x y)) (c (let ([zz (fresh-sym 'z)]) `(ex ,zz (and (pr Nat ,zz) ,(Op kind x y zz)))))
         (lambda (z _1 H1)
           (define-values (cl cex)
             (if (eq? kind 'add)
                 (values (ru "H:SucEx" z) (c (let ([zz (fresh-sym 'z)]) `(ex ,zz (pr Suc ,zz ,z)))))
                 (values (lu '(Tot add) z x) (c (let ([zz (fresh-sym 'z)]) `(ex ,zz (and (pr Nat ,zz) ,(add-f z x zz))))))))
           (obt H1 (list cl) cex
             (lambda (z3 _2 H2)
               (T (list (lu `(S ,kind) x y z y2 z3) (ru "H:NatSuc" y y2) (lu `(Uq ,kind) x y2 z2 z3)
                        (leib `(not ,(Cst kind x z HOLE)) z2 z3) (ex-i z goal))
                  (Imp H2 goal)))))))))))

;; NatOp: Nat x & Nat y & Op(x,y,z) -> Nat z       x y z = 0..2
(define (knat! kind)
  (define key `(NatOp ,kind))
  (need key
   (lambda ()
    (ktot! kind) (kuq! kind)
    (lemma! key 3
     (lambda ()
       (define-values (x y z) (values 0 1 2))
       (define H0 (c `(and (pr Nat ,x) (pr Nat ,y) ,(Op kind x y z))))
       (obt H0 (list (lu `(Tot ,kind) x y)) (c (let ([zz (fresh-sym 'z)]) `(ex ,zz (and (pr Nat ,zz) ,(Op kind x y zz)))))
         (lambda (z0 _ H1)
           (T (list (lu `(Uq ,kind) x y z z0) (leib `(not (pr Nat ,HOLE)) z z0)) (Imp H1 (c `(pr Nat ,z)))))))))))

(define (kind-all! kind)
  (for ([f (list kbase! kstep! kex! ktot! kuq! ks! kz! kzinv! ksinv! knat!)]) (f kind)))
