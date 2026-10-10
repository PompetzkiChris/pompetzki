#lang racket/base
;; omega-kind-v1.rkt -- lane L7, item 4: the recursion lemmas of Add and Mul (sigma1's definitions) for all of omega.
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

(define (kinds-uq-hyps kind x y) (if (eq? kind 'add) (list (Nat y)) (list (Nat x) (Nat y))))

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
       (define hyp `(and (pr Emp ,o) (pr Opr ,p ,o ,z0) (pr Sng ,f ,p)))
       (define hypc (c hyp))
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
       (define Gin `(and ,(Body kind f x o z0) ,(Dm f o)))
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
       (define hyp `(and ,(Body kind f x y z) ,(Dm f y) (pr Suc ,y2 ,y) ,(Cst kind x z z2) (pr Opr ,p ,y2 ,z2) ,(Un g f p)))
       (define hypc (c hyp))
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
                                         (leib `(not (in ,HOLE ,y)) y i) (rs "L:NoSelf" y)
                                         (inst* (c (list-ref partsF 3)) (list i j a b))))
                           (Imp hypc (c `(imp (in ,i ,y) ,(match Mx [_ 'X]))))))
                      caseA))))
       st)))))
